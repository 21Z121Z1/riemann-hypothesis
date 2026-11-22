import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScKey
section
noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_ne_zero_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K U : Subgroup G}
    (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

section Key

variable {n a b : ℕ}

theorem parabolic_function_right_invariant (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (g y : GLw n w) (hy : y ∈ GlobalTheory.LFun.KGL w n) (k : GLw a w × GLw b w)
    (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w a) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w b) (hd : CtLevel.dgM h w k ∈ K')
    (m : GLw a w × GLw b w) : phi3 h w f g y (m * k) = phi3 h w f g y m := by
  have hab : absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    (absHalf_blockDet_KGL_invariant E a b w m k hk1 hk2).2
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (g⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (g⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w m k _).2]
    have hc : y⁻¹ * CtLevel.dgM h w k * y ∈ K' := by simpa using hN y⁻¹ (inv_mem hy) _ hd
    have e2 : g⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * CtLevel.dgM h w k) * y =
        1 * (g⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k * y) := by group
    rw [e2, hf _ K'.one_mem _ hc]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (g⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k.1 k.2⁻¹ hk1 (inv_mem hk2)]

theorem parabolic_function_left_invariant (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g) (g y : GLw n w) (k : GLw n w) (hk : k ∈ K') :
    phi3 h w f (g * k) y = phi3 h w f g y := by
  funext m
  unfold phi3
  congr 2
  funext X
  have e : (g * k)⁻¹ * blk h w m (Multiplicative.toAdd X) * y =
      k⁻¹ * (g⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * 1 := by group
  rw [e, hf _ (inv_mem hk) _ K'.one_mem]

theorem parabolic_function_transform (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (g y : GLw n w) (m₀ : GLw a w × GLw b w)
    (X₀ : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (m : GLw a w × GLw b w) :
    phi3 h w f (blk h w m₀ X₀ * g) y m =
      absHalf w (m₀.1.val.det ^ b / m₀.2.val.det ^ a) * phi3 h w f g y (m₀⁻¹ * m) := by
  have hA := GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w
  have hmul : absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) =
      absHalf w (m₀.1.val.det ^ b / m₀.2.val.det ^ a) *
        absHalf w ((m₀⁻¹ * m).1.val.det ^ b / (m₀⁻¹ * m).2.val.det ^ a) := by
    rw [hA, hA, hA, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
  set m' := m₀⁻¹ * m with hm'
  set C : Matrix (Fin a) (Fin b) (w.adicCompletion E) := (m'.1⁻¹).val * X₀ * m'.2.val with hC
  have hb : ∀ Y : Matrix (Fin a) (Fin b) (w.adicCompletion E), blk h w m Y = blk h w m₀ X₀ * blk h w m' (-C + Y) := by
    intro Y
    rw [GlobalTheory.LeviFubini.blk_mul_blk, hm', mul_inv_cancel_left, ← hm', ← hC]
    congr 1
    abel
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f ((blk h w m₀ X₀ * g)⁻¹ * blk h w m (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (g⁻¹ * blk h w m' (Multiplicative.toAdd Y) * y)) (Multiplicative.ofAdd (-C) * X) := by
    funext X
    rw [hb]
    congr 1
    simp only [toAdd_mul, toAdd_ofAdd]
    group
  unfold phi3
  rw [hmul, e, GlobalTheory.CompanionTheory.CtMulSplit.hint_left (intMat a b w) (Multiplicative.ofAdd (-C))
    (fun Y => f (g⁻¹ * blk h w m' (Multiplicative.toAdd Y) * y))]
  ring

def fv (h : a + b = n) (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W) (f : GLw n w → ℂ) (X : Finset (GLw n w)) (v : GLw n w → W)
    (g : GLw n w) : W :=
  ∑ y ∈ X, (((U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : ℕ) : ℂ))⁻¹ •
    ∑ᶠ q : (GLw a w × GLw b w) ⧸ U, phi3 h w f g y q.out • ρ q.out (v y)

theorem lw_fv (h : a + b = n) (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W) (f : GLw n w → ℂ) (hfc : HasCompactSupport f)
    (X : Finset (GLw n w)) (v : GLw n w → W) (g : GLw n w)
    (hUK : U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (hne : U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0)
    (hinv : ∀ y ∈ X, ∀ k ∈ U, ∀ m, phi3 h w f g y (m * k) = phi3 h w f g y m)
    (hvU : ∀ y ∈ X, ∀ k ∈ U, ρ k (v y) = v y) (lw : W →ₗ[ℂ] ℂ) :
    lw (fv h w U ρ f X v g) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
      fun m => phi3 h w f g y m * lw (ρ m (v y)) := by
  unfold fv
  rw [map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets U hUo _ (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w f hfc g y)
  rw [map_smul, smul_eq_mul, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ U _ hUK ?_ hne,
    map_finsum lw (hfin.subset fun q hq h0 => hq (by
      show phi3 h w f g y q.out • ρ q.out (v y) = 0
      rw [h0, zero_smul]))]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [map_smul, smul_eq_mul]
  · intro k hk m
    show phi3 h w f g y (m * k) * lw (ρ (m * k) (v y)) = phi3 h w f g y m * lw (ρ m (v y))
    rw [hinv y hy k hk, map_mul, Module.End.mul_apply, hvU y hy k hk]

end Key

section Key2

variable {n a b : ℕ}

theorem fv_right (h : a + b = n) (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g) (X : Finset (GLw n w)) (v : GLw n w → W)
    (g k : GLw n w) (hk : k ∈ K') : fv h w U ρ f X v (g * k) = fv h w U ρ f X v g := by
  unfold fv
  simp only [parabolic_function_left_invariant h w K' f hf g _ k hk]

theorem fv_law (h : a + b = n) (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W) (f : GLw n w → ℂ) (hfc : HasCompactSupport f)
    (X : Finset (GLw n w)) (v : GLw n w → W)
    (hUK : U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (hne : U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0)
    (hinv : ∀ g, ∀ y ∈ X, ∀ k ∈ U, ∀ m, phi3 h w f g y (m * k) = phi3 h w f g y m)
    (hvU : ∀ y ∈ X, ∀ k ∈ U, ρ k (v y) = v y) (m₀ : GLw a w × GLw b w)
    (X₀ : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    fv h w U ρ f X v (blk h w m₀ X₀ * g) =
      absHalf w (m₀.1.val.det ^ b / m₀.2.val.det ^ a) • ρ m₀ (fv h w U ρ f X v g) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun lw => ?_
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul,
    lw_fv h w U ρ f hfc X v _ hUK hUo hne (hinv _) hvU lw]
  have e2 := lw_fv h w U ρ f hfc X v g hUK hUo hne (hinv g) hvU (lw ∘ₗ ρ m₀)
  rw [LinearMap.comp_apply] at e2
  rw [e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← GlobalTheory.CompanionTheory.CtMulSplit.hint_left _ m₀]
  simp only [parabolic_function_transform, inv_mul_cancel_left, map_mul, Module.End.mul_apply, LinearMap.comp_apply]
  have e3 := GlobalTheory.CompanionTheory.HeckeAct.hint_mul_const ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
    (fun m => phi3 h w f g y m * lw (ρ m₀ (ρ m (v y)))) (absHalf w (m₀.1.val.det ^ b / m₀.2.val.det ^ a))
  rw [mul_comm, ← e3]
  congr 1
  funext m
  ring

end Key2

theorem key_ind {n a b : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hK'o : IsOpen (K' : Set (GLw n w)))
    (hK'le : K' ≤ GlobalTheory.LFun.KGL w n) (hnorm : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (X : Finset (GLw n w)) (hXK : ∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) (hX : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K')
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W) (e : GLw n w → ℂ)
    (he : IsHk K' e) (U₀ : Subgroup (GLw a w × GLw b w)) (hU₀ : IsOpen (U₀ : Set (GLw a w × GLw b w)))
    (v : GLw n w → W) (hv : ∀ y ∈ X, v y ∈ fixed ρ U₀) :
    ∃ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ,
      lw (u.1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => phi3 h w e x y m * lw (ρ m (v y)) := by
  obtain ⟨hKa, hKac⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w a
  obtain ⟨hKb, hKbc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w b
  set K2' : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) with hK2'
  set U : Subgroup (GLw a w × GLw b w) := U₀ ⊓ K2' ⊓ K'.comap (CtLevel.dgM h w) with hUdef
  have hUK : U ≤ K2' := fun k hk => hk.1.2
  have hK2o : IsOpen (K2' : Set (GLw a w × GLw b w)) := by
    rw [hK2', Subgroup.coe_prod]; exact hKa.prod hKb
  have hK2c : IsCompact (K2' : Set (GLw a w × GLw b w)) := by
    rw [hK2', Subgroup.coe_prod]; exact hKac.prod hKbc
  have hUo : IsOpen (U : Set (GLw a w × GLw b w)) := by
    rw [hUdef, Subgroup.coe_inf, Subgroup.coe_inf, Subgroup.coe_comap]
    exact (hU₀.inter hK2o).inter (hK'o.preimage (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.continuous_dgM h w))
  have hne : U.relIndex K2' ≠ 0 := relIndex_ne_zero_open hK2c hUo
  have hf := he.2.2.2
  have hinv : ∀ g, ∀ y ∈ X, ∀ k ∈ U, ∀ m, phi3 h w e g y (m * k) = phi3 h w e g y m := by
    intro g y hy k hk m
    have hk2 : k ∈ K2' := hk.1.2
    rw [hK2', Subgroup.mem_prod] at hk2
    exact parabolic_function_right_invariant h w K' hnorm e hf g y (hXK y hy) k hk2.1 hk2.2 hk.2 m
  have hvU : ∀ y ∈ X, ∀ k ∈ U, ρ k (v y) = v y := by
    intro y hy k hk
    have := hv y hy ⟨k, hk.1.1⟩
    simpa using this
  set F : GLw n w → W := fv h w U ρ e X v with hF
  set H := GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
  set σ : Representation ℂ H W := (GlobalTheory.SmGL.twist (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom)
          (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)))).comp
          (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))
  have hlaw : F ∈ GlobalTheory.PRep.indSpace H σ := by
    intro p g
    set m₀ := GlobalTheory.LeviFubini.levH h w p with hm₀
    have hp1 : GlobalTheory.LeviFubini.levH h w ((GlobalTheory.LeviFubini.sM h w m₀)⁻¹ * p) = 1 := by
      rw [map_mul, map_inv, GlobalTheory.LeviFubini.levH_sM, inv_mul_cancel]
    obtain ⟨X₀, hX₀⟩ := GlobalTheory.LeviFubini.exists_uN h w _ hp1
    have hp : (p : GLw n w) = blk h w m₀ (Multiplicative.toAdd X₀) := by
      rw [← GlobalTheory.LeviFubini.sM_mul_uN, hX₀, mul_inv_cancel_left]
    show F (p * g) = σ p (F g)
    rw [hp, hF, fv_law h w U ρ e he.2.2.1 X v hUK hUo hne hinv hvU m₀ _ g]
    simp only [σ, MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m₀]
    rfl
  have hsm : (⟨F, hlaw⟩ : GlobalTheory.PRep.indSpace H σ) ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    refine GlobalTheory.CompanionTheory.NodeSep.isOpen_fix (GlobalTheory.PRep.ind H σ) hK'o fun k hk => Subtype.ext (funext fun g => ?_)
    change F (g * k) = F g
    exact fv_right h w U ρ K' e hf X v g k hk
  let u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) := ⟨⟨F, hlaw⟩, hsm⟩
  refine ⟨u, ?_, fun x hx lw => ?_⟩
  · intro k
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show F (g * k) = F g
    exact fv_right h w U ρ K' e hf X v g k k.2
  · show lw (F x) = _
    exact lw_fv h w U ρ e he.2.2.1 X v x hUK hUo hne (hinv x) hvU lw

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScLin
section
noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {U : Subgroup G} {v : V} : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro hv u hu
    have := hv ⟨u, hu⟩
    simpa using this
  · intro hv u
    simpa using hv u u.2

theorem actP_eq_sum (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) :
    ∃ (S : Subgroup (GLw a w × GLw b w)) (s : Finset ((GLw a w × GLw b w) ⧸ S)),
      S ≤ U ∧ S ≤ K2 a b w ∧ S.relIndex (K2 a b w) ≠ 0 ∧ (∀ q, q ∉ s → u q.out = 0) ∧
      actP w u G = ((S.relIndex (K2 a b w) : ℕ) : ℂ)⁻¹ • ∑ q ∈ s, u q.out • pairRt a b w q.out G := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w
  set S : Subgroup (GLw a w × GLw b w) := K2 a b w ⊓ U with hSdef
  have hSo : IsOpen (S : Set (GLw a w × GLw b w)) := hKo.inter hUo
  have hidx : S.relIndex (K2 a b w) ≠ 0 :=
    GlobalTheory.FunObj.relIndex_inf_ne_zero (N := K2 a b w) (O := U) (C := K2 a b w) hUo hKc le_rfl le_rfl
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets S hSo u hu
  set s := hfin.toFinset with hsdef
  have hs : ∀ q, q ∉ s → u q.out = 0 := fun q hq => by
    by_contra h0
    exact hq (hfin.mem_toFinset.2 h0)
  have hGf := (mem_fixed_iff'.1 hG)
  refine ⟨S, s, inf_le_right, inf_le_left, hidx, hs, ?_⟩
  funext z
  have hr : S ≤ rStab (fun m => u m * pairRt a b w m G z) := by
    intro k hk g
    show u (g * k) * pairRt a b w (g * k) G z = u g * pairRt a b w g G z
    rw [hur g k (Subgroup.mem_inf.1 hk).2, map_mul, Module.End.mul_apply, hGf k (Subgroup.mem_inf.1 hk).2]
  rw [actP, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ inf_le_left hr hidx]
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem lw_actP (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GLw a w × GLw b w) Y) (Λ : (H E a b → ℂ) →ₗ[ℂ] Y)
    (hΛ : ∀ g, Λ (pairRt a b w g G) = τ g (Λ G)) (lw : Y →ₗ[ℂ] ℂ) :
    lw (Λ (actP w u G)) = hint (K2 a b w) (fun m => u m * lw (τ m (Λ G))) := by
  obtain ⟨S, s, hSU, hSK, hidx, hs, hEq⟩ := actP_eq_sum w U hUo G hG u hu hur
  have hGf := (mem_fixed_iff'.1 hG)
  have hr : S ≤ rStab (fun m => u m * lw (τ m (Λ G))) := by
    intro k hk g
    show u (g * k) * lw (τ (g * k) (Λ G)) = u g * lw (τ g (Λ G))
    rw [hur g k (hSU hk), map_mul, Module.End.mul_apply, ← hΛ k, hGf k (hSU hk)]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ hSK hr hidx, hEq, map_smul, map_smul, map_sum, map_sum,
    smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, map_smul, hΛ, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem extTensor_twRep {G₁ G₂ V₁ V₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂) (χ₁ : G₁ →* ℂˣ) (χ₂ : G₂ →* ℂˣ)
    (g : G₁ × G₂) (x : V₁ ⊗[ℂ] V₂) :
    GlobalTheory.SmGL.extTensor (twRep ρ₁ χ₁) (twRep ρ₂ χ₂) g x = (((χ₁ g.1 : ℂˣ) : ℂ) * ((χ₂ g.2 : ℂˣ) : ℂ)) •
      GlobalTheory.SmGL.extTensor ρ₁ ρ₂ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v₁ v₂ =>
    simp only [GlobalTheory.SmGL.extTensor_tmul, twRep_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
      mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem mu_fac (μ : HChar E) (w : Pl E) (m : GLw a w × GLw b w) :
    ((μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ) : ℂ) =
      ((μ.loc w ((-1) ^ (a * b)) : ℂˣ) : ℂ) *
        ((((((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 : ℂˣ) : ℂ) *
          (((((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 : ℂˣ) : ℂ)) := by
  have hb : ∀ x, (μ ^ b).loc w x = μ.loc w x ^ b := fun x => rfl
  have ha : ∀ x, (μ ^ a).loc w x = μ.loc w x ^ a := fun x => rfl
  simp [map_mul, map_pow, mul_assoc, hb, ha]

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
end

