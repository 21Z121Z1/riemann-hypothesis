import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0533
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0057
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacter
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem hgp_twist_tE {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j n : ℕ} (h : (i + 1) + j = n)
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HGPg k h)
    (hq : (1 : GL (Fin (n + 1)) k) * ((g : Mir k n) : GL (Fin (n + 1)) k) * (1 : GL (Fin (n + 1)) k)⁻¹ ∈
      parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g (tE V W v) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  have hL : leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩ =
      leviTwo k (Fin (i + 1)) (Fin (j + 1)) ((gpProjg k h g).1, ((gpProjg k h g).2 : GL (Fin (j + 1)) k)) := by
    have e : (⟨_, hq⟩ : parab k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1)))) = hgpInclg k h g :=
      Subtype.ext (by simp [hgpInclg])
    rw [e]
    funext x
    cases x <;> rfl
  have key : ∀ x : ∀ b, TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    set g₁ : GL (Fin (i + 1)) k := (gpProjg k h g).1 with hg₁
    set g₂ : Mir k j := (gpProjg k h g).2 with hg₂
    have hl : ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
        ((twist π₁ (dpow (i + 1) (((j + 1 : ℕ) : ℝ) / 2)) g₁ (x false) : V) ⊗ₜ[ℂ]
          (twist (π₂.comp (Mir k j).subtype) (dpowM j (-((i + 1 : ℕ) : ℝ) / 2)) g₂ (x true) : W) : V ⊗[ℂ] W) :=
      (congrArg _ (Exponents.boolTensorEquiv_tprod x)).trans (extTensor_tmul _ _ _ _ _)
    have hr : tE V W (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviTwo k (Fin (i + 1)) (Fin (j + 1)) (g₁, (g₂ : GL (Fin (j + 1)) k))) : ℂˣ) : ℂ) •
          ((π₁ g₁ (x false) : V) ⊗ₜ[ℂ] (π₂ (g₂ : GL (Fin (j + 1)) k) (x true) : W) : V ⊗[ℂ] W) := by
      show tE V W (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))))
        (leviProj k (two (stdSum (by omega : (i + 1) + (j + 1) = n + 1))) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [hL, twist_apply, piTensor_tprod, map_smul]
      exact congrArg _ (Exponents.boolTensorEquiv_tprod _)
    rw [hl, hr, deltaHalf_two]
    simp only [twist_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, MonoidHom.comp_apply,
      Units.val_mul, dpow, dpowM, detChar_apply]
    have c₁ : ((((j + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = (Fintype.card (Fin (j + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    have c₂ : ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = -(Fintype.card (Fin (i + 1)) : ℂ) / 2 := by
      rw [Fintype.card_fin]
      push_cast
      rfl
    rw [c₁, c₂, mul_comm]
    rfl
  have := LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext key) :
    ((((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h)) g) ∘ₗ (tE V W).toLinearMap) =
      (tE V W).toLinearMap ∘ₗ (sQ (by omega : (i + 1) + (j + 1) = n + 1) π₁ π₂ ⟨_, hq⟩)) v
  exact this

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterion
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

theorem eLast_vecMul {k : Type} [Field k] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [eLast, vecMul, dotProduct, Pi.single_apply]

theorem mem_two_iff {k : Type} [Field k] {r t N : ℕ} (h : r + t = N) (g : GL (Fin N) k) :
    g ∈ parab k (two (stdSum h)) ↔
      ∀ a b : Fin N, r ≤ (a : ℕ) → (b : ℕ) < r → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hg a b ha hb
    have hlt : (a : ℕ) - r < t := by have := a.isLt; omega
    have ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a := Fin.ext (by rw [stdSum_inr]; simp only []; omega)
    have eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b := Fin.ext (by rw [stdSum_inl])
    have := mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)
    rw [two_true, two_false, ea, eb] at this
    exact this
  · intro hg
    refine mem_parab_iff.2 ?_
    intro x y u v hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
    refine hg _ _ ?_ ?_
    · show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)
      rw [stdSum_inr]; omega
    · show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r
      rw [stdSum_inl]; exact v.isLt

theorem mem_dcos_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔
      ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  intro k _ _ _ _ i t h ht g
  have hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ) := by
    rw [Fin.val_last]; omega
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩ a
    have hpi : p⁻¹ ∈ Mir k (i + t) := inv_mem hp
    have hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        eLast k (i + t) := hpi
    have e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹ := by simp
    have h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
      rw [Units.val_mul, ← vecMul_vecMul, hpi']
    have hrow := (eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))
    rw [e]
    refine (congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)
    rw [stdSum_inl]; exact a.isLt
  · intro hy
    classical
    let y : Fin (i + t + 1) → k :=
      ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))
    have hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
      have : y = vecMul (eLast k (i + t))
          ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := (eLast_vecMul _ _).symm
      rw [this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
    have hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0 := by
      intro c hc
      have e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c := Fin.ext (by rw [stdSum_inl])
      have := hy ⟨(c : ℕ), hc⟩
      rw [e] at this
      exact this
    obtain ⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : y = 0 := funext hcon
      rw [h0, zero_vecMul] at hyg
      have := congrFun hyg (Fin.last (i + t))
      simp [eLast] at this
    have hblock : i + 1 ≤ (a₀ : ℕ) := by
      by_contra hlt
      exact ha₀ (hfirst a₀ (by omega))
    let σ : Equiv.Perm (Fin (i + t + 1)) := Equiv.swap a₀ (Fin.last (i + t))
    have hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ) := by
      intro r hr
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · exact hlast
      · exact hblock
      · exact hr
    let B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
      ((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id
    have hdet : B.det ≠ 0 := by
      simp only [B]
      rw [Matrix.det_permute, det_updateRow_one]
      refine mul_ne_zero ?_ ha₀
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    let b : GL (Fin (i + t + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B := rfl
    have hbQ : b ∈ parab k (two (stdSum h)) := by
      refine (mem_two_iff h b).2 fun r c hr hc => ?_
      rw [hb]
      simp only [B, submatrix_apply, id]
      by_cases e : σ r = a₀
      · rw [e, updateRow_self]
        exact hfirst c hc
      · rw [updateRow_ne e, one_apply_ne]
        intro e2
        have := hσ r hr
        rw [e2] at this
        omega
    refine ⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩
    show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)
    have hB : B (Fin.last (i + t)) = y := by
      funext c
      simp [B, σ]
    rw [Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]
    exact hyg

end GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCoset
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem dcos_compact_lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}
    (hL : LocSec Q P x) (hP : IsClosed (P : Set G)) (B₀ : Set G) (hB : IsCompact B₀) (hB₁ : B₀ ∈ 𝓝 (1 : G))
    (D : Set G) (hD : IsCompact D) (hDc : D ⊆ dcos Q P x) :
    ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  obtain ⟨O, hO, hsec⟩ := hL Set.univ Filter.univ_mem B₀ hB₁
  have hemb : Topology.IsClosedEmbedding (Subtype.val : P → G) := hP.isClosedEmbedding_subtypeVal
  have hC₁ : IsCompact ((Subtype.val : P → G) ⁻¹' B₀) := hemb.isCompact_preimage hB
  refine hD.induction_on
    (p := fun T => ∃ C : Set P, IsCompact C ∧ ∀ g ∈ T, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c)
    ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, hC, h⟩
    exact ⟨C, hC, fun g hg => h g (hST hg)⟩
  · rintro S T ⟨C, hC, h⟩ ⟨C', hC', h'⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    rintro g (hg | hg)
    · obtain ⟨q, hq, c, hc, e⟩ := h g hg
      exact ⟨q, hq, c, Or.inl hc, e⟩
    · obtain ⟨q, hq, c, hc, e⟩ := h' g hg
      exact ⟨q, hq, c, Or.inr hc, e⟩
  · intro g₀ hg₀
    obtain ⟨q₀, hq₀, p₀, hp₀, e₀⟩ := hDc hg₀
    have hcont : Continuous fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹ := by fun_prop
    have hval : (q₀ * x)⁻¹ * g₀ * p₀⁻¹ = 1 := by
      rw [e₀]; group
    have hU : (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O ∈ 𝓝 g₀ :=
      hcont.continuousAt.preimage_mem_nhds (by rw [hval]; exact hO)
    refine ⟨D ∩ (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O,
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
      (fun c : P => c * (⟨p₀, hp₀⟩ : P)) '' ((Subtype.val : P → G) ⁻¹' B₀),
      hC₁.image (by fun_prop), ?_⟩
    rintro g ⟨hgD, hgU⟩
    obtain ⟨q', hq', p', hp', e'⟩ := hDc hgD
    have hxu : x * ((q₀ * x)⁻¹ * g * p₀⁻¹) ∈ dcos Q P x := by
      refine ⟨q₀⁻¹ * q', Q.mul_mem (Q.inv_mem hq₀) hq', p' * p₀⁻¹, P.mul_mem hp' (P.inv_mem hp₀), ?_⟩
      rw [e']; group
    obtain ⟨s, hs, -, p₂, hp₂, hp₂B, e₂⟩ := hsec _ hgU hxu
    refine ⟨q₀ * s, Q.mul_mem hq₀ hs, ⟨p₂, hp₂⟩ * ⟨p₀, hp₀⟩, ⟨⟨p₂, hp₂⟩, hp₂B, rfl⟩, ?_⟩
    have e₃ : g = q₀ * (x * ((q₀ * x)⁻¹ * g * p₀⁻¹)) * p₀ := by group
    rw [e₃, e₂]
    simp [mul_assoc]

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormulaStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_hecke_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ctT_split_eq | exact GlobalTheory.CompanionTheory.CtS.ctT_split_eq | (intros; apply GlobalTheory.CompanionTheory.CtS.ctT_split_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionSmoothLieDerivativeStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_smooth_lie_derivative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ → convR μ (tst U β) Fl ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspDiscreteDecompositionGL
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRep

theorem cuspDiscreteDecompositionGL : GlobalTheory.Published.CuspDiscreteDecompositionGL :=
  GlobalTheory.T.cuspidal_decomposition_of_compact GlobalTheory.T.cuspidal_convolution_compact

end GlobalTheory.CompanionTheory.CuspRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfColouring
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProdCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_class_of_degree (n : ℕ) (t : IrrGL k) (h : t.1 = n) :
    ∃ u : IrrCl (GL (Fin n) k), (⟨n, u⟩ : IrrGL k) = t := by
  subst h
  exact ⟨t.2, rfl⟩

theorem subsingleton_irrCl_of_eq_zero (n : ℕ) (h : n = 0) : Subsingleton (IrrCl (GL (Fin n) k)) := by
  subst h
  exact GlobalTheory.SmGL.SegModel.subsingleton_irrCl_zero

theorem class_eq_of_sigma_eq (t : IrrGL k) (z : IrrCl (GL (Fin t.1) k))
    (h : (⟨t.1, z⟩ : IrrGL k) = t) : z = t.2 :=
  eq_of_heq (Sigma.ext_iff.1 h).2

set_option maxHeartbeats 1600000 in

theorem jhMult_cell_colour : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL k) (W : List (IrrGL k)) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  intro k _ _ _ _ h x W b hrow hcol c hb
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hC : CellSemisimplification k := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2
  obtain ⟨T, hT0, hT⟩ := hC (Fin h) (Fin W.length) (fun i => Fin (x i).1) (fun j => Fin (W.get j).1)
    (fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i))
    (fun j => stdBlocks (fun i => b i j) (hcol j)) (fun i => (x i).2.rep.V) (fun i => (x i).rep)
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength)
  have hirr : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (W.get j).2.rep
  let τ : IrrRep (Levi k fun j => Fin (W.get j).1) :=
    ⟨_, piTensor fun j => (W.get j).rep, isSmooth_piTensor fun j => (W.get j).2.rep.smooth, hirr⟩
  refine (hT τ).trans ?_
  have hzero : ∀ i j, c j ≠ i → b i j = 0 := fun i j hij => by rw [hb, if_neg hij]

  have hcolumn : ∀ (s : ∀ i j, IrrCl (GL (Fin (b i j)) k)) (j : Fin W.length),
      ∃ z : IrrCl (GL (Fin (W.get j).1) k), (⟨_, z⟩ : IrrGL k) = ⟨b (c j) j, s (c j) j⟩ ∧
        Nonempty ((multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s i j).rep.ρ).Equiv z.rep.ρ) := fun s j =>
    GlobalTheory.T.product_single_nonzero_factor_equiv (fun i => (⟨b i j, s i j⟩ : IrrGL k)) (hcol j) (c j)
      fun i hi => hzero i j (Ne.symm hi)

  have hex : ∀ i j, ∃ u : IrrCl (GL (Fin (b i j)) k),
      c j = i → (⟨b i j, u⟩ : IrrGL k) = W.get j := by
    intro i j
    by_cases hij : c j = i
    · obtain ⟨u, hu⟩ := exists_class_of_degree (b i j) (W.get j) (by rw [hb, if_pos hij])
      exact ⟨u, fun _ => hu⟩
    · exact ⟨(IrrRep.det (Fin (b i j)) 1 isSmoothChar_one).cl, fun h' => absurd h' hij⟩
  choose s₀ hs₀ using hex
  have hfirst : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ)
      (jac (stdBlocks (b i) (hrow i)) (x i).rep) = jmL (sub W c i) (x i).rep := fun i =>
    GlobalTheory.T.jacquet_multiplicity_sublist_padding W c i (fun j => (⟨b i j, s₀ i j⟩ : IrrGL k)) (fun j hj => hs₀ i j hj)
      (fun j hj => hzero i j hj) (hrow i) (x i).rep
  rw [Finset.sum_eq_single s₀]
  · choose z hz e using hcolumn s₀
    have hzW : ∀ j, z j = (W.get j).2 := fun j =>
      class_eq_of_sigma_eq _ _ ((hz j).trans (hs₀ (c j) j rfl))
    have hsecond : jhMult τ.ρ (piTensor fun j =>
        multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s₀ i j).rep.ρ) = 1 := by
      have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s₀ i j).rep.ρ).Equiv (piTensor fun j => (W.get j).rep) :=
        LocGL.piTensorEquiv fun j => (e j).some.trans (by rw [hzW j]; exact .refl _)
      exact (jhMult_congr_right _ a).trans (jhMult_self hirr)
    rw [hsecond, mul_one]
    exact Finset.prod_congr rfl fun i _ => hfirst i
  · intro s _ hs
    refine mul_eq_zero_of_right _ ?_
    choose z hz e using hcolumn s
    have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
        fun i => (s i j).rep.ρ).Equiv (piTensor fun j => (z j).rep.ρ) :=
      LocGL.piTensorEquiv fun j => (e j).some
    refine (jhMult_congr_right _ a).trans ?_
    by_contra hne
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 hne).nonempty_equiv hirr
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (z j).rep)
    have hcl : ∀ j, (W.get j).2 = z j := fun j => by
      have := GlobalTheory.T.tensor_product_determines_factor_classes _ (fun j => GL (Fin (W.get j).1) k) (fun j => (W.get j).2.rep)
        (fun j => (z j).rep) ⟨φ.symm⟩ j
      rwa [IrrCl.cl_rep, IrrCl.cl_rep] at this
    refine hs (funext fun i => funext fun j => ?_)
    by_cases hij : c j = i
    · subst hij
      have h1 : (⟨b (c j) j, s (c j) j⟩ : IrrGL k) = ⟨b (c j) j, s₀ (c j) j⟩ := by
        rw [hs₀ (c j) j rfl, ← hz j, ← hcl j]
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    · haveI := subsingleton_irrCl_of_eq_zero (k := k) (b i j) (hzero i j hij)
      exact Subsingleton.elim _ _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.CompanionTheory.FineProdCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrix
section
noncomputable section

namespace GlobalTheory.CompanionTheory.CuspCell

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

theorem exists_eq_singleton_of_sum {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem exists_equiv_of_sums {l c : ℕ} {A : Type*} {x : Fin l → A} {y : Fin c → A} {t : Fin l → Fin c → Multiset A}
    (hr : ∀ i, ({x i} : Multiset A) = ∑ j, t i j) (hc : ∀ j, ({y j} : Multiset A) = ∑ i, t i j) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, t i j = if e j = i then {x i} else 0 := by
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum (hr i)
  choose e he1 he0 using fun j => exists_eq_singleton_of_sum (hc j)
  have hne : ∀ {a : A}, ({a} : Multiset A) ≠ 0 := Multiset.singleton_ne_zero _
  have h1 : ∀ i, e (r i) = i := fun i => by
    by_contra hi
    exact hne ((hr1 i).symm.trans (he0 (r i) i (Ne.symm hi)))
  have h2 : ∀ j, r (e j) = j := fun j => by
    by_contra hj
    exact hne ((he1 j).symm.trans (hr0 (e j) j (Ne.symm hj)))
  refine ⟨⟨e, r, h2, h1⟩, fun a => ?_, fun i j => ?_⟩
  · have h3 := hr1 (e a)
    rw [h2 a, he1 a] at h3
    exact Multiset.singleton_inj.1 h3
  · by_cases h : e j = i
    · subst h
      have h3 := hr1 (e j)
      rw [h2 j] at h3
      simpa using h3
    · simpa [h] using he0 j i (Ne.symm h)

theorem exists_equiv_of_jhMult_cell_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin c → Multiset (IrrGL k), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, ({y j} : Multiset (IrrGL k)) = ∑ i, t i j :=
    fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (hasSupport_self (hyc j)) (hC j)
  obtain ⟨e, he, het⟩ := exists_equiv_of_sums hAt hU
  refine ⟨e, he, fun i j => ?_⟩
  have hd := (ht i j).sum_fst
  rw [het i j] at hd
  split_ifs at hd ⊢ <;> simpa using hd.symm

end GlobalTheory.CompanionTheory.CuspCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOrderBoundedHeckeSupportStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_order_bounded_hecke_support : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ordL_det_range | exact GlobalTheory.CompanionTheory.CtS.ordL_det_range | (intros; apply GlobalTheory.CompanionTheory.CtS.ordL_det_range <;> assumption)
end

