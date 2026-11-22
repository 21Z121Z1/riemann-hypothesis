import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GlobalLocalFactorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplitAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem mulVec_sec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (u : Fin n → k) :
    M *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((M.map p.pr *ᵥ u) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm (u j)]

theorem mulVec_csec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (z : Fin n → k) :
    M *ᵥ (fun i => cA D (p.sec (z i))) = fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec, map_mul, cA_cA]

theorem eq_sec_add_csec {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = p.v)) :
    y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff p (y i)).1 (hy i)
  simp only [Pi.add_apply, p.sec_pr, map_mul, cA_cA]
  rw [← add_mul, h]

variable {p}

theorem mulVec_mem_of_parts {S T : HSp D} {L : Lat S} {L' : Lat T} (hL : IsSelfDualC S L)
    (M : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    (hw : ∀ u, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) → (fun i => p.sec ((M.map p.pr *ᵥ u) i)) ∈ latV T L' (· = p.v))
    (hc : ∀ z, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) →
      (fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV T L' (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = p.v)) : M *ᵥ y ∈ latV T L' (· = p.v) := by
  have e := eq_sec_add_csec p (FrameLat.latV_supp hy)
  rw [e] at hy ⊢
  have h := (FrameLat.decomp hL _ _).1 hy
  rw [Matrix.mulVec_add, mulVec_sec, mulVec_csec]
  exact add_mem (hw _ h.1) (hc _ h.2)

theorem pair_eq (S : HSp D) (x z : Fin S.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j =
      x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, RingHom.comp_apply, mul_assoc]

theorem conjT_map {m n : Type} (M : Matrix m n D.host.E) :
    Mᴴ.map (p.pr.comp ((cA D).comp (incA D))) = (M.map (p.pr.comp (incA D)))ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, RingHom.comp_apply, FrameLat.cA_incA,
    star_star]

end GlobalTheory.LineSplitAt

namespace GlobalTheory.LineSplitAt

set_option maxHeartbeats 1000000 in

theorem orthAt_of_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  intro D k _ _ _ _ p n' _ _ S A L o ζ _ α α₀ hsum _ LA LS ΛA hLA hLS hα hα₀
  have hb : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hsum
  have hPJ : o.pA.map p.pr * o.jA.map p.pr = 1 := by
    rw [← Matrix.map_mul, o.pA_jA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz : o.pA.map p.pr *ᵥ (⇑p.pr ∘ ratV (vecB o ζ)) = 0 := by
    have e1 : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      simp only [ratV, vecB, OrthDec.jB, rat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    funext i
    rw [← RingHom.map_mulVec, e1, Matrix.mulVec_mulVec, o.pA_jB, Matrix.zero_mulVec]
    simp
  have hPz : o.pA.map p.pr * replicateCol (Fin 1) (fun i => p.pr (ratV (vecB o ζ) i)) = 0 := by
    ext i j
    have := congrFun hz i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

  have hwA : ∀ u : Fin A.rank → k, (fun i => p.sec (u i)) ∈ latV A LA (· = p.v) →
      (fun i => p.sec ((o.jA.map p.pr *ᵥ u) i)) ∈ latV S LS (· = p.v) := by
    intro u hu
    have hx : α.b' *ᵥ u ∈ ΛA := (hα _).2 (by rwa [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec])
    have e : o.jA.map p.pr *ᵥ u = α₀.b *ᵥ Sum.elim (α.b' *ᵥ u) 0 := by
      rw [hb, Matrix.fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb',
        Matrix.mul_one, Matrix.mulVec_zero, add_zero]
    rw [e]
    exact (hα₀ _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hx, by simp⟩)
  have hwS : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S LS (· = p.v) →
      (fun i => p.sec ((o.pA.map p.pr *ᵥ u) i)) ∈ latV A LA (· = p.v) := by
    intro u hu
    have hy : α₀.b' *ᵥ u ∈ lastKer ΛA := (hα₀ _).2 (by rwa [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec])
    have e : o.pA.map p.pr *ᵥ u = α.b *ᵥ ((α₀.b' *ᵥ u) ∘ Sum.inl) := by
      conv_lhs => rw [← Matrix.one_mulVec u, ← α₀.bb', ← Matrix.mulVec_mulVec, hb, Matrix.fromCols_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPJ, Matrix.one_mul, Matrix.mulVec_mulVec _ (o.pA.map p.pr), hPz,
        Matrix.zero_mulVec, add_zero]
    rw [e]
    exact (hα _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).1

  have hG2 : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  have hG1 : S.gram * o.iA = o.qAᴴ * A.gram := by
    have := congrArg Matrix.conjTranspose hG2
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, gram_conjTranspose] at this
    exact this.symm
  have hcA : ∀ z : Fin A.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV A LA (· = p.v) →
      (fun i => cA D (p.sec ((o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV S LS (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLS _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * (o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.pA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (A.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.iA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.qA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG1, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLA z).1 hz _ (hwS x hx)
  have hcS : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S LS (· = p.v) →
      (fun i => cA D (p.sec ((o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV A LA (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLA _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (A.gram i j))) * (o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.jA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.qA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.iA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG2, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLS z).1 hz _ (hwA x hx)
  have h1 : ∀ y ∈ latV A LA (· = p.v), o.jA *ᵥ y ∈ latV S LS (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLA o.jA hwA hcA hy
  have h2 : ∀ y ∈ latV S LS (· = p.v), o.pA *ᵥ y ∈ latV A LA (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLS o.pA hwS hcS hy
  have hsplit : ∀ g : Fin S.rank → AE D, o.jA *ᵥ (o.pA *ᵥ g) + o.jB *ᵥ (o.pB *ᵥ g) = g := fun g => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  let fB := (mulVecLin o.qB).restrictScalars (𝓞 D.host.E)
  have h3 : ∀ x ∈ latV L (LS.map fB) (· = p.v), o.jB *ᵥ x ∈ latV S LS (· = p.v) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, ha', c, hc, w, hw, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨s, hs, rfl⟩ := hw
      have hg : (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) ∈ latV S LS (· = p.v) :=
        AddSubgroup.subset_closure ⟨a, ha, ha', 1, rfl, s, hs, rfl⟩
      have e2 : o.pB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) =
          fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] o.qB i j) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show o.jB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i)) ∈ _
      rw [← e2]
      have hm := hg
      rw [← hsplit (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i))] at hm
      exact (add_mem_cancel_left (h1 _ (h2 _ hg))).1 hm
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx
  refine ⟨LS.map fB, fun y => ⟨fun hy => ⟨h2 y hy, GlobalTheory.OrthSumLat.rat_mulVec_mem_latV o.qB
    (fun x hx => Submodule.mem_map_of_mem hx) hy⟩, fun h => ?_⟩⟩
  rw [← hsplit y]
  exact add_mem (h1 _ h.1) (h3 _ h.2)

end GlobalTheory.LineSplitAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContrLocProof
open GlobalTheory.ContractionLocal

theorem contrLoc : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  have hH := GlobalTheory.T.besselLineContraction_heisenberg_invariant
  have hC := GlobalTheory.T.lineRow_translation_heisenberg_splitPlace
  have hD := GlobalTheory.T.splitPlace_lineColumn_translation_heisenberg
  have hL := GlobalTheory.T.besselLine_contraction_thetaFunction_isLocalModel
  have hR := GlobalTheory.T.thetaContraction_isLocalModel_secondVariable
  intro D hCF k _ _ _ _ _ _ p ν hν ψ hψ ψk hk ρ σ B B' l S vL s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' hF hF' T₁ T₂ hT₁ hT₂
  obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψkc, hψk1⟩ := hψk ψk hk
  let Bm := contrBil hψ l S vL T₁ T₂ hT₁.theta hT₂.theta
  have inv1 : ∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = (ψk (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro u₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hC D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' u₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) :=
      hT₁.modul _ hx2 Ψ₁ Ψ₁' fun t => by rw [h1, hx3]
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) := by
      rw [← hx1]; exact hT₂.trans _ Ψ₂ Ψ₂' h2
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  have inv2 : ∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψk (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro y₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hD D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' y₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) := by
      rw [← hx1]; exact hT₁.trans _ Ψ₁ Ψ₁' h1
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) :=
      hT₂.modul _ hx2 Ψ₂ Ψ₂' fun t => by rw [h2, hx3]
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  obtain ⟨Λ, hΛ⟩ := hCF k ψk ν hψkc hψk1 hν n n' n'' (WO B.A S → WO S B'.A → ℂ) Bm inv1 inv2
  obtain ⟨φ₀, φ₀', hφ⟩ := exists_normPair ψk ν hψkc hν n
  have hval : ∀ Ξ₁ Ξ₂ (Ξ : SB (Matrix n n' k × Matrix n'' n k)), (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) →
      Λ Ξ = Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) := by
    intro Ξ₁ Ξ₂ Ξ hq
    obtain ⟨Ξ', hΞ'1, hΞ'2⟩ := hΛ (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂)
    have : Ξ' = Ξ := Subtype.ext (funext fun q => by rw [hΞ'1, contr_tens, hφ, mul_one, hq])
    rw [← this, hΞ'2]
  refine ⟨Λ, ⟨fun Ξ₂ v => ?_, fun Ξ₁ u => ?_⟩, hΛ⟩
  · let T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
      { toFun := fun Ξ₁ u => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext u; simp only [map_add, LinearMap.add_apply, Pi.add_apply]
        map_smul' := fun c a => by funext u; simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hL D k p ψ hψ ρ σ B B' l S vL s hs n n' FA F₀ FS hF T₁ hT₁ φ₀ _ (hT₂.theta _) v T fun Ξ₁ u => rfl,
      fun Ξ₁ Ξ hq u => ?_⟩
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
  · let T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ) :=
      { toFun := fun Ξ₂ v => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext v; simp only [map_add, Pi.add_apply]
        map_smul' := fun c a => by funext v; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hR D k p ψ hψ ρ σ B B' l S vL (s * p.xi) ?_ n n'' FS FA' F₀' hF' T₂ hT₂ φ₀' _ (hT₁.theta _) u T
      fun Ξ₂ v => rfl, fun Ξ₂ Ξ hq v => ?_⟩
    · obtain ⟨-, -, hxi, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
      exact mul_ne_zero hs hxi
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
end GlobalTheory.ContrLocProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]

open Formalism.IndefR.Eqv in

theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finset_sum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni

open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in

theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDivEqRelIndex
section
noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' I : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype I] [DecidableEq I] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.PlaceCompare

end

noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

def eX (κ t j : ℕ) : XI κ t j ≃ XIx (Fin κ) (Fin t) j :=
  (Equiv.sumAssoc _ _ _).symm.trans (((Equiv.refl _).sumCongr Fin.revPerm).sumCongr (Equiv.refl _))

def eY (κ t j c : ℕ) : XI κ t j ⊕ Fin c ≃ XIx (Fin κ) (Fin t) j ⊕ Fin c := (eX κ t j).sumCongr (Equiv.refl _)

def ord (κ t : ℕ) {l : ℕ} (j c : ℕ) (h : j + c = l) : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ XI κ t j ⊕ Fin c :=
  (stdOrd (Fin κ) (Fin t) j c h).trans (eY κ t j c).symm

def labIx {κ t l j : ℕ} : Ix (Fin κ ⊕ Fin l) (Fin t) j → Fin κ ⊕ ℕ ⊕ ℕ × Fin t
  | .inl (.inl a) => .inl a
  | .inl (.inr i) => .inr (.inl (i.val + 1))
  | .inr p => .inr (.inr (p.1.val, p.2))

variable {κ t l j c : ℕ}

def aOrd (h : j + c = l) : Fin κ ⊕ Fin j ⊕ Fin c → Fin κ ⊕ Fin l
  | .inl a => .inl a
  | .inr (.inl s) => .inr ⟨c + (j - 1 - s.val), by omega⟩
  | .inr (.inr i) => .inr ⟨i.val, by omega⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFrame {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (b : ℕ → kˣ) (o : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) :=
  ⟨o, embA n (SplitFlip.diagGL fun i => b (i.val + 1))⟩

variable {s : ℕ} (S : SymData k s κ)

abbrev levelChain (t : ℕ) : Chain k s (XI κ t) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) (s + 2)) :=
  Chain.ofType S.P S.μ S.tame (fun j c h => typeFrame S.ϖ (ord κ t j c h)) (LatFrame.refl k _)

variable (s κ t) in

abbrev ramChain (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) :
    Chain k s (XI κ t) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) (s + 2)) :=
  Chain.ofTwist δ hδ η (fun j c h => plainFrame (ord κ t j c h)) (LatFrame.refl k _)

variable {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ)

def prodShiftedUnits (b : ℕ → kˣ) (c : ℕ) : kˣ := ∏ i : Fin c, b (i.val + 1)

end GlobalTheory.PlaceCompare

end

noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' m m' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m] [DecidableEq m]
  [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sumE (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

section Frames

omit [MeasurableSpace k] [BorelSpace k]

end Frames

structure Renum {s : ℕ} {X X' : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] [∀ j, Fintype (X' j)]
    [∀ j, DecidableEq (X' j)] {Z : Type} [Fintype Z] [DecidableEq Z] (e : ∀ j, X j ≃ X' j) (T : Chain k s X Z)
    (T' : Chain k s X' Z) : Prop where
  mu : T.mu = T'.mu
  bas : ∀ j c h, reGL (sumE (e j) c) (T.bas j c h) = T'.bas j c h
  mem : ∀ j c h g, g ∈ (T.lev j c h).J ↔ reGL (sumE (e j) c) g ∈ (T'.lev j c h).J
  lam : ∀ j c h g hg hg', (T.lev j c h).lam ⟨g, hg⟩ = (T'.lev j c h).lam ⟨reGL (sumE (e j) c) g, hg'⟩
  Phi : ∀ j c h y, T.Phi j c h (y.submatrix (sumE (e (j + 1)) c) (sumE (e j) (c + 1))) = T'.Phi j c h y

end GlobalTheory.PlaceCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMeasureUniformInTuple_of_thetaLiftScalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  first | exact @GlobalTheory.RealMeasOne.one_real_measure | exact GlobalTheory.RealMeasOne.one_real_measure | (intros; apply GlobalTheory.RealMeasOne.one_real_measure <;> assumption)
end

