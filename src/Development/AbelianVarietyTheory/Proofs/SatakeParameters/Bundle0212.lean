import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

abbrev sz (r t : ℕ) : Fin 2 → ℕ := ![r, t]

theorem sum_sz (r t : ℕ) : ∑ a, sz r t a = r + t := by simp [sz]

def blocks2 (r t : ℕ) : (Σ a : Fin 2, Fin (sz r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sz r t)

theorem blocks2_zero (r t : ℕ) (i : Fin r) : blocks2 r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 0 i).trans ?_
  simp

theorem blocks2_one (r t : ℕ) (j : Fin t) : blocks2 r t ⟨1, j⟩ = Fin.natAdd r j := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 1 j).trans ?_
  simp [sz]

theorem twoE_false (r t : ℕ) (i : Fin r) : two (stdSum (rfl : r + t = r + t)) ⟨false, i⟩ = Fin.castAdd t i := by
  ext; simp

theorem twoE_true (r t : ℕ) (j : Fin t) : two (stdSum (rfl : r + t = r + t)) ⟨true, j⟩ = Fin.natAdd r j := by
  ext; simp

end GlobalTheory.JacBlockTwo

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inl' (r t : ℕ) (i : Fin r) : stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := by
  ext; simp

theorem stdSum_inr' (r t : ℕ) (j : Fin t) : stdSum (rfl : r + t = r + t) (Sum.inr j) = Fin.natAdd r j := by
  ext; simp

def IsUpperUnip {r t : ℕ} (g : GL (Fin (r + t)) k) : Prop :=
  (∀ (i : Fin t) (j : Fin r), (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.castAdd t j) = 0) ∧
  (∀ i j : Fin r, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.castAdd t i) (Fin.castAdd t j) =
    (1 : Matrix (Fin r) (Fin r) k) i j) ∧
  (∀ i j : Fin t, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.natAdd r j) =
    (1 : Matrix (Fin t) (Fin t) k) i j)

theorem mem_unipRad_two {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (two (stdSum (rfl : r + t = r + t))) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_two]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← stdSum_inl', ← stdSum_inr']; exact h0 i j
    · rw [← twoE_false, ← twoE_false]; exact hD false i j
    · rw [← twoE_true, ← twoE_true]; exact hD true i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j i => ?_, ?_⟩
    · have := h0 j i; rwa [← stdSum_inl', ← stdSum_inr'] at this
    · rintro (_ | _) i j
      · have := h1 i j; rwa [← twoE_false, ← twoE_false] at this
      · have := h2 i j; rwa [← twoE_true, ← twoE_true] at this

theorem mem_unipRad_blocks2 {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (blocks2 r t) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← blocks2_one, ← blocks2_zero]; exact h0 1 0 i j (by decide)
    · rw [← blocks2_zero, ← blocks2_zero]; exact hD 0 i j
    · rw [← blocks2_one, ← blocks2_one]; exact hD 1 i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · match a, b with
      | 0, 0 => intro i j hab; exact absurd hab (lt_irrefl _)
      | 0, 1 => intro i j hab; exact absurd hab (by decide)
      | 1, 0 => intro i j _; rw [blocks2_one r t i, blocks2_zero r t j]; exact h0 i j
      | 1, 1 => intro i j hab; exact absurd hab (lt_irrefl _)
    · match a with
      | 0 => intro i j; rw [blocks2_zero r t i, blocks2_zero r t j]; exact h1 i j
      | 1 => intro i j; rw [blocks2_one r t i, blocks2_one r t j]; exact h2 i j

theorem unipRad_blocks2 (r t : ℕ) :
    unipRad k (blocks2 r t) = unipRad k (two (stdSum (rfl : r + t = r + t))) := by
  ext g; rw [mem_unipRad_blocks2, mem_unipRad_two]

theorem unipRad_two_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (two (stdSum (rfl : r + t = r + t))) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨h0, h1, h2⟩ := mem_unipRad_two.1 hh.1
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by ext i j; exact h2 i j
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply]) 1
    (by rw [hsub, det_one, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

theorem mulSingle_mem_KO {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) (a : Bool) :
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) a ∈ KO k (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _
  · rw [Pi.mulSingle_eq_same]; exact hg

theorem deltaHalf_mulSingle {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    deltaHalf k (Two (Fin r) (Fin t)) (Pi.mulSingle true g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_mem_KO (r := r) hg a)

theorem act_mulSingle {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    π (leviEmb k (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle true g)) v =
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (two (stdSum (rfl : r + t = r + t)))
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_mem_KO hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_mem_KO hg a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [← twoE_true, ← twoE_false]
    exact leviEmb_apply_ne k _ _ (by decide) _ _
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Matrix (Fin r) (Fin r) k) i j :=
    fun i j => by
      rw [← twoE_false, ← twoE_false, hdef, leviEmb_apply_same, Pi.mulSingle_eq_of_ne (by decide)]
      rfl
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = g.val := by
    ext i j
    rw [Matrix.submatrix_apply, ← twoE_true, ← twoE_true, hdef, leviEmb_apply_same, Pi.mulSingle_eq_same]
  exact hv h hKO (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply])
    (Matrix.GeneralLinearGroup.det g) (by rw [hsub, Matrix.GeneralLinearGroup.val_det_apply])

theorem jacquet_ne_zero_of_isBlockVec_two : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  intro hP k _ _ _ _ r t χ V _ _ π v hsm hirr hχ hv0 hv
  refine ⟨?_, ?_⟩
  · intro hx
    apply hv0
    have hx' : (Submodule.Quotient.mk v : Jacquet π (unipRad k (blocks2 r t))) = 0 := by
      rw [unipRad_blocks2]; exact hx
    refine hP k (r + t) 2 (sz r t) (blocks2 r t) ⟨V, π, hsm, hirr⟩ v ?_ hx'
    rw [unipRad_blocks2]
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_two_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro g hg
    rw [jac_mk, deltaHalf_mulSingle hg, act_mulSingle hv hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlockTwo

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharacters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem forall_val_of_heq_hom {E : Type} [Field E] {a b b' : ℕ} (hb : b = b') (P : ℂ → Prop)
    {f : HomE E a b → ℂ} {g : HomE E a b' → ℂ} (h : HEq f g) (hg : ∀ x, P (g x)) : ∀ x, P (f x) := by
  subst hb
  rw [eq_of_heq h]
  exact hg

theorem kernel_datum_of_hecke_character_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ
  obtain ⟨hFG, hsd⟩ := GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual D L hT Gi Gl K Y cX ex t
  refine ⟨hFG, fun u μ i hi c c' hpin => ⟨hsd u μ i c, hsd u μ (i + 1) c', ?_⟩⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, row, -, hyb, hE, hC1, -, hC2, -, hp⟩ := t.rd_chain u μ
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · intro x
    rw [hE i hlt c c' x]
    exact GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) i hlt _ _ _ _ x
  · subst heq
    intro x
    rw [hC1 c c' x]
    exact GlobalTheory.T.precedingStepDatum_integral_away_from_levels D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) _ _ _ _ x
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    obtain ⟨d, hd⟩ := (hp c').1 hpin
    refine forall_val_of_heq_hom (congrArg D.R.N (by omega : t.m2 + 1 + 1 = D.R.m))
      (IntOff (t.O u μ).S) (hC2 c c' d hd) fun x => ?_
    exact GlobalTheory.T.lastStep_data_integralAwayFrom_levels D L hT Gi Gl K Y cX ex t u μ _ _ d x (hyb c)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplit
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.KerRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime

theorem kerTh_common : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime

theorem eqOffSplit_refl (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : GL3Theta.EqOffSplit D L L :=
  ⟨1, one_ne_zero, fun Q hQ => (Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hQ isUnit_one)).elim,
    fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem eqOffSplit_symm {D : D7} {n : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : GL3Theta.EqOffSplit D L₁ L₂) : GL3Theta.EqOffSplit D L₂ L₁ := by
  obtain ⟨a, ha0, hsa, ha1, ha2⟩ := h
  exact ⟨a, ha0, hsa, ha2, ha1⟩

theorem mem_Th_const_mul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F : TaylorLogMetric.VC D a b → ℂ} (hF : F ∈ TaylorLogMetric.Th D T L L') (k : ℂ) :
    (fun z => k * F z) ∈ TaylorLogMetric.Th D T L L' := by
  refine ⟨hF.1.const_mul k, fun x hx z => ?_⟩
  have := hF.2 x hx z
  simp only [TaylorLogMetric.U] at this ⊢
  rw [← this]; ring

theorem chiFac_ne_zero (D : D7) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {a b : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : Base.chiFac χ a b L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h))
    (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h'))

theorem thMoved_move_right (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
  have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h' h'', mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h h'') e

theorem thMoved_move_left (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h₁ : StandardLatticesGL3.SD D L₁) (h' : StandardLatticesGL3.SD D L') :
    B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
  have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h h₁, mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h₁ h') e

theorem kerTh_relation_of_indicator : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  intro D cc δ B χ hcc hδ hδ0 hχ hL hV hE hModel hMoves SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN c hrel z
  obtain ⟨T, hT⟩ := kerTh_common D cc δ B χ hcc hδ hδ0 hL hV SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι N N' hN
  obtain ⟨ha, hb, h0, h0'⟩ := hA0
  have hth0 : B.thMoved a b N₀ N₀' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) N₀ N₀' := by
    have hm := mem_Th_const_mul D (TaylorLogMetric.tor0 D cc δ) (hV a b N₀ N₀' ⟨ha, hb, h0, h0'⟩).1 (Base.chiFac χ a b N₀ N₀')⁻¹
    convert hm using 1
    funext w
    show _ = _ * (Base.chiFac χ a b N₀ N₀' * _)
    rw [← mul_assoc, inv_mul_cancel₀ (chiFac_ne_zero D hχ h0 h0'), one_mul]
  obtain ⟨Xi, -, hXi⟩ := hModel cc δ hcc hδ a b N₀ N₀' ⟨ha, hb, h0, h0'⟩ P hP _ hth0
  have hmove : ∀ i, B.thMoved a b (N i) (N' i) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor N₀ N₀') (TaylorLogMetric.La D B.tor (N i) (N' i)) (B.thMoved a b N₀ N₀') := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, ho, ho'⟩ := hN i
    rw [thMoved_move_right D cc δ B χ hχ hE ha hb (N i) N₀' (N' i) hi h0' hi',
      thMoved_move_left D cc δ B χ hχ hE ha hb N₀ (N i) N₀' h0 hi h0']
    exact hMoves cc δ hcc hδ a b N₀ (N i) (N i) N₀' N₀' (N' i) ⟨ha, hb, h0, h0'⟩ ⟨ha, hb, hi, h0'⟩ ⟨ha, hb, hi, hi'⟩
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho)) (eqOffSplit_refl D _) (eqOffSplit_refl D _)
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho')) _ hth0
  have key : ∀ i, ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) *
      (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z =
      T (Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1)) z := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, -, -⟩ := hN i
    set s : ℂ := ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) with hs
    set X := Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1) with hX
    have hm : B.thMoved a b (N i) (N' i) = fun w => s⁻¹ * X w := by
      rw [hmove i, hXi (N i) (N' i) ⟨ha, hb, hi, hi'⟩ (hN i).2.1 (hN i).2.2]
      funext w
      push_cast
      rfl
    have he : B.eNat χ a b (N i) (N' i) = (Base.chiFac χ a b (N i) (N' i) * s⁻¹) • X := by
      funext w
      show Base.chiFac χ a b (N i) (N' i) * B.thMoved a b (N i) (N' i) w = _
      rw [hm, Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hs0 : s ≠ 0 := by
      intro h0s
      apply (hV a b (N i) (N' i) ⟨ha, hb, hi, hi'⟩).2.1
      rw [he, h0s, inv_zero, mul_zero, zero_smul]
    rw [hT i, he, map_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [chiFac_ne_zero D hχ hi hi']
  simp_rw [key]
  have hsum := congrArg (fun f => T (Xi f) z) hrel
  simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  exact hsum

end GlobalTheory.KerRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EigenFactor

section Avg

variable {H W W' : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def avgOp (σ : Representation ℂ H W) (θ : H →* ℂˣ) (U : Subgroup H) [Fintype (H ⧸ U)] : W →ₗ[ℂ] W :=
  ∑ q : H ⧸ U, (((θ q.out)⁻¹ : ℂˣ) : ℂ) • σ q.out

end Avg

section Tensor

variable {β : Type} [Fintype β] [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)]

end Tensor

theorem exists_eig_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first
  | exact @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | (apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector ..)

end GlobalTheory.EigenFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInertStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  first | exact @GlobalTheory.KerStd.HypCoord.norm_hK_le_one | exact GlobalTheory.KerStd.HypCoord.norm_hK_le_one | (intros; apply GlobalTheory.KerStd.HypCoord.norm_hK_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_orthogonality_of_form : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  first | exact @GlobalTheory.ThetaExh.typeOrth_of_pin | exact GlobalTheory.ThetaExh.typeOrth_of_pin | (intros; apply GlobalTheory.ThetaExh.typeOrth_of_pin <;> assumption)
end

