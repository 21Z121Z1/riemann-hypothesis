import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LowerBlockParam

variable {D : D7}

theorem val_lev {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V}
    (hκ : κ ∈ Lev.levG s.V s.β s.L) (g : GA D s.V) :
    PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  have hκ' : κ ∈ levS s.V s.β s.L := hκ
  show (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v (g * κ) = _ * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g
  rw [← hu]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    rw [hM.lev f κ hκ' g]; ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]; ring

theorem chart_fin : ∀ (D : D7) (s : PiLocalization₂ D) (j : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V), IsChart s j φ ι → ∀ y, ι y ∈ GfC s.V := by
  intro D s j v φ ι hι y
  obtain ⟨ε, -, hy⟩ := hι
  rw [← (hy y).1]
  exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _

theorem hecke_keeps : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι →
    ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v)))
      (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ),
      GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ u : s.CC c, ∃ u' : s.CC c, ∀ v',
        PiLocalization₂.val u' v' = fun h => ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * PiLocalization₂.val u v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR u
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  let T' : MMap s.M := ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) • heckeOn s.M {ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)} T
  have hT'v : ∀ vv h, T' vv h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * T vv (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
    intro vv h
    simp [T', heckeOn, postOn_apply, heckeLin_apply]
  have h0 : T' ∈ Mult c.θ s.M ∅ (Lev.levChi s.V s.β s.L) := by
    refine Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact GlobalTheory.HeckeParts.isMultMap_heckeOn hM
      (fun a ha => by rw [Finset.mem_singleton] at ha; subst ha; exact chart_fin D s j v φ ι hι _) (fun _ _ hk => hk.elim)
  have h1 := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').1 h0
  have hIs : IsMultMap c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) T' := by
    refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
    intro vv κ hκ g
    rw [hT'v, hT'v]
    exact GlobalTheory.T.lowerBlockDoubleCosetOperator_keeps_levelCharacter D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR (T vv) (fun κ hκ g => hM.lev vv κ hκ g) κ hκ g
  refine ⟨⟨PiTensorProduct.lift T', (mem_multT _ _ _ _ _).2 (by
    rw [LinearEquiv.symm_apply_apply]; exact (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').2 hIs)⟩, fun v' => ?_⟩
  funext h
  show PiTensorProduct.lift T' v' h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e))
  rw [← hu]
  induction v' using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, hT'v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]

theorem qOfVal : ∀ D : D7, SoftQ D → QOfVal D := by
  intro D hS c w hw j hj s hs
  obtain ⟨-, -, hinj, -⟩ := hS c w hw j hj s hs
  have hdict := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw j hj s hs
  have htype : ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl,
      LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ,
      (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → ∀ (u : s.CC c) v' g,
        PiLocalization₂.val u v' (g * ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) * PiLocalization₂.val u v' g := by
    intro PP hPP v φ hφ ξl hξ ι hι y hy d hd u v' g
    obtain ⟨-, -, -, -, hch⟩ := hdict PP hPP v φ hφ
    obtain ⟨-, hlev, hchi⟩ := hch ι hι
    rw [val_lev u v' ((hlev y).2 hy) g, hchi ξl hξ y hy d hd]

  have hπ : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V) y
      (F : GA D s.V → ℂ), ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) y F = fun h => F (h * ι y) := by
    intro v ι y F; rfl
  clear hdict
  refine ⟨?_, ?_⟩
  · intro x v0 hne hQ v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    obtain ⟨hty0, hcard, hT0⟩ := hQ PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    clear hQ
    obtain ⟨g0, hg0⟩ := Function.ne_iff.1 hne
    have hunit : ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → starRingEnd ℂ (((ξl d)⁻¹ : ℂˣ) : ℂ) = ((ξl d : ℂˣ) : ℂ) := by
      intro y hy d hd
      have h1 := congrFun (hty0 y hy d hd) g0
      rw [hπ] at h1
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v0 g0, map_mul] at h1
      exact mul_right_cancel₀ ((map_ne_zero _).2 hg0) h1
    refine ⟨?_, hcard, ?_⟩
    · intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, map_mul, hunit y hy d hd]
    · intro S R dd hR
      have e0 := hT0 S R dd hR
      obtain ⟨u', hu'⟩ := hecke_keeps D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ (GlobalTheory.ParHecke.indic S) R dd hR x
      generalize GlobalTheory.ParHecke.genVal _ _ _ _ _ = c0 at e0 ⊢
      have hcoef : ∀ y ∈ R, starRingEnd ℂ ((ξl (dd y) : ℂˣ) : ℂ) = (((ξl (dd y))⁻¹ : ℂˣ) : ℂ) := by
        intro y hy
        rw [← hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2, Complex.conj_conj]
      have hv0 : PiLocalization₂.val u' v0 = (starRingEnd ℂ c0) • PiLocalization₂.val x v0 := by
        rw [hu']; funext h
        have := congrArg (starRingEnd ℂ) (congrFun e0 h)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at this
        simp only [map_sum (starRingEnd ℂ), (starRingEnd ℂ).map_mul, Complex.conj_conj] at this
        rw [Pi.smul_apply, smul_eq_mul, this]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2]
      have hv0ne : v0 ≠ 0 := by
        rintro rfl; exact hne (by simp [PiLocalization₂.val])
      have heq : u' = (starRingEnd ℂ c0) • x := by
        refine sub_eq_zero.1 (hinj _ v0 hv0ne ?_)
        simp only [PiLocalization₂.val, Submodule.coe_sub, Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply] at hv0 ⊢
        rw [hv0, sub_self]
      funext h
      have := congrArg (starRingEnd ℂ) (congrFun (hu' v') h)
      rw [heq] at this
      simp only [PiLocalization₂.val, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, (starRingEnd ℂ).map_mul,
        Complex.conj_conj, map_sum (starRingEnd ℂ)] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ]
      refine this.trans (Finset.sum_congr rfl fun y hy => ?_)
      rw [hcoef y hy]
  · intro hj0 x v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    subst hj0
    have hE : IsEmpty (Blocks 0 D.R.t) := ⟨fun b => b.1.elim0⟩
    have hd1 : ∀ y : GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → d = 1 := by
      intro y d hd; ext; rw [hd, Matrix.det_isEmpty]; rfl
    have hty : (fun g => starRingEnd ℂ (PiLocalization₂.val x v' g)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.typeSpace ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) ξl := by
      intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, hd1 y d hd]
      simp
    refine ⟨hty, ?_, ?_⟩
    · show (0 : Multiset ℂˣ).card = _
      simp
    · intro S R dd hR
      have hS0 : S = ∅ := Finset.eq_empty_of_isEmpty S
      subst hS0
      have hfun : (fun i : Fin D.R.r ⊕ Blocks 0 D.R.t => ϖ ^ (Sum.elim (0 : Fin D.R.r → ℤ) (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) i)) = 1 := by
        funext i
        rcases i with i | i
        · simp
        · exact isEmptyElim i
      have hg : (GlobalTheory.ZonalCellDecomposition.mtor ϖ (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) :
          GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v)) = 1 := by
        unfold GlobalTheory.ZonalCellDecomposition.mtor GlobalTheory.GLDoubling.torusElt
        rw [hfun, map_one]
      rw [hg] at hR ⊢
      obtain ⟨j0, ⟨hj0R, -⟩, huniq⟩ := hR.2 1 (one_mem _)
      have hRs : R = {j0} := by
        ext y; simp only [Finset.mem_singleton]; constructor
        · intro hy; exact huniq y ⟨hy, by simpa using inv_mem (hR.1 y hy).1⟩
        · rintro rfl; exact hj0R
      subst hRs
      rw [Finset.sum_singleton, mul_one, hty j0 (hR.1 j0 hj0R).1 (dd j0) (hR.1 j0 hj0R).2, smul_smul]
      have hq : qPar c PP xx 0 = 0 := rfl
      simp [GlobalTheory.ParHecke.genVal, hq, Multiset.esymm]

end GlobalTheory.LowerBlockParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevOfRed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.RedLev

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := by
  simp [Formalism.L2.DIV.frGL]

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul (F := D.host.F) (E := D.host.E) β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem conj_eq {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k n Y) (bas W : GL Y k) (σ : Fin n ≃ Y)
    (N : Matrix (Fin n) (Fin n) k)
    (h : F.β * W.val * F.γ * (F.β * bas.val).submatrix id σ = (F.β * bas.val).submatrix id σ * N) :
    (bas⁻¹ * W * bas).val.submatrix σ σ = N := by
  have h1 : ((bas⁻¹).val * F.γ).submatrix σ id * (F.β * bas.val).submatrix id σ = 1 := by
    change ((bas⁻¹).val * F.γ * (F.β * bas.val)).submatrix σ σ = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul, Matrix.submatrix_one_equiv]
  rw [← Matrix.one_mul N, ← h1, Matrix.mul_assoc, ← h]
  change _ = ((bas⁻¹).val * F.γ * (F.β * W.val * F.γ * (F.β * bas.val))).submatrix σ σ
  congr 1
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ F.β bas.val, ← Matrix.mul_assoc F.γ F.β, F.γβ, Matrix.one_mul, Matrix.one_mul]

end

end GlobalTheory.SeeSaw.RedLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTarget
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem cj_smul {X Y : Type} (e : Y → X) (c : ℂ) (φ : X → ℂ) : cj e (c • φ) = starRingEnd ℂ c • cj e φ := by
  funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem cj_dagger_inj (S T : HSp D) {a b : WO S T → ℂ} (h : cj (dagger T S) a = cj (dagger T S) b) : a = b := by
  have h' := congrArg (cj (dagger S T)) h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T), cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at h'

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conj_psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : AF D.host.F) :
    starRingEnd ℂ (ψ (-q)) = ψ q := by
  rw [← Complex.inv_eq_conj (hψ.1.2.1 _), AddChar.map_neg_eq_inv, inv_inv]

theorem conj_levi_coeff' (z : Circle) (r : ℝ) :
    starRingEnd ℂ ((z : ℂ) * (r : ℂ)) = ((z⁻¹ : Circle) : ℂ) * (r : ℂ) := by
  rw [map_mul, Circle.coe_inv_eq_conj, Complex.conj_ofReal]

theorem incA_conj_neg_inv : cA D (incA D (-D.host.xi0⁻¹)) = incA D D.host.xi0⁻¹ := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem dagger_ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) :
    dagger S T (ofAdj S T z) = incA D D.host.xi0⁻¹ • z := by
  rw [dagger, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, incA_conj_neg_inv, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem symplOH_dagger {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  rw [symplOH, symplOH, (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).1 x y, mul_neg]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

theorem nC_inv_incAdj_sub {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    mt T (d.nC c)⁻¹ ⬝ d.incAdj S y - d.incAdj S y =
      d.incX S (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) := by
  rw [d.nC_inv, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, d.nC_jY,
    Matrix.add_mul, add_sub_cancel_left, AddSubgroup.coe_neg, Matrix.mul_assoc, Matrix.neg_mul]

theorem giA_adj_central {S : HSp D} {ρ : ℕ} (c : skewA D ρ) (y : Mx D S.rank ρ) :
    giA S ⬝ adj (-(c.1 ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)))) = (incA D D.host.xi0⁻¹ • y) ⬝ c.1 := by
  have hc : adj c.1 = -c.1 := c.2
  rw [adj_neg, adj_mul, hc, adj_smul, adj_mul, adj_adj, adj_gA, incA_conj_neg_inv]
  simp only [Matrix.mul_neg, neg_neg]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, giA_gA_cancel, Matrix.smul_mul]

theorem quadratic_form_xi_inverse {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.qS S c (incA D D.host.xi0⁻¹ • y) = -d.qT S c y := by
  obtain ⟨μ', 𝓕', -, hX, hY, -, -⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  rw [HypDec.qS, HypDec.qT, ← hX, ← giA_adj_central c y, ← hY, nC_inv_incAdj_sub, symplOH_dagger hψ]

end GlobalTheory.MixTargetProof

namespace GlobalTheory.MixTargetProof

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

section Read

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} {d : HypDec T T₀ ρ} {χS : (AE D)ˣ →* Circle}
  {om : Rep S T} {om₀ : Rep S T₀} {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
  {μ' : Measure (Mx D S.rank ρ)} {𝓕' : Set (Mx D S.rank ρ)} {f : WO S T → ℂ}
  (hsw : ∀ (f : WO S T → ℂ) y, d.mixS S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) =
    cj (dagger T₀ S) (d.mixT S ψ μ 𝓕 f y))
  (FS : FormulasS d ψ χS (conjAdjoint om) (conjAdjoint om₀) μ' 𝓕' (cj (dagger T S) f))
include hsw FS

theorem read_source (g : GA D S) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (g, 1) f) y = om₀ (g, 1) (d.mixT S ψ μ 𝓕 f (mt S g⁻¹ ⬝ y)) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.target g (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.mul_smul, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_core (h₀ : GA D T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.emb0 h₀) f) y = om₀ (1, h₀) (d.mixT S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.core h₀ (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, hsw, conjAdjoint_cj] at h1
  exact h1

theorem read_levi (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.levi a) f) y =
      (((χS (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        d.mixT S ψ μ 𝓕 f (y ⬝ a.1) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.levi a (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw] at h1
  rw [cj_smul, conj_levi_coeff']
  exact h1

theorem read_unip (hψ : IsStdChar D ψ (-1)) (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.nB b) f) y = heisO ψ S T₀ (ofAdj S T₀ (y ⬝ b)) (d.mixT S ψ μ 𝓕 f y) := by
  apply cj_dagger_inj S T₀
  have h1 := FS.unip b (incA D D.host.xi0⁻¹ • y)
  rw [conjAdjoint_cj, hsw, Matrix.smul_mul, hsw, ← dagger_ofAdj, (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T₀).2.2.2] at h1
  exact h1

theorem read_centre (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (c : skewA D ρ)
    (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (om (1, d.nC c) f) y = ψ (d.qT S c y) • d.mixT S ψ μ 𝓕 f y := by
  apply cj_dagger_inj S T₀
  have h1 : d.mixS S ψ μ' 𝓕' (conjAdjoint om (d.nC c, 1) (cj (dagger T S) f)) (incA D D.host.xi0⁻¹ • y) =
      ψ (d.qS S c (incA D D.host.xi0⁻¹ • y)) • d.mixS S ψ μ' 𝓕' (cj (dagger T S) f) (incA D D.host.xi0⁻¹ • y) :=
    FS.centre c _
  rw [conjAdjoint_cj, hsw, hsw, quadratic_form_xi_inverse hψ d μ 𝓕 hμ] at h1
  rw [cj_smul, ← conj_psi_neg hψ, Complex.conj_conj]
  exact h1

end Read

theorem mixedTarget : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedTarget D := by
  intro D ψ S T T₀ ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ f hf
  have hψ := hom.std
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hF : IsThetaFunO ψ T S (cj (dagger T S) f) := ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1 f).2 hf
  have FS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ T T₀ S ρ d χT χS (conjAdjoint om) (conjAdjoint om₀)
    (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om hom) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T₀ χS χT om₀ hom₀) μ' 𝓕' hμ' _ hF
  exact ⟨read_source hsw FS, read_core hsw FS, read_levi hsw FS, read_unip hsw FS hψ, read_centre hsw FS hψ hμ⟩

end GlobalTheory.MixTargetProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.TopLocFac

open Formalism.IndefR.Lev Formalism.IndefR.Mult in

theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
    (g : Geo D) (hψ : IsStdChar D R.ψ (-1)) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, sBF := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
     sFB := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some, io := fun _ => 0, ioT := fun _ _ => 0 }⟩

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }⟩

theorem isLocFac_xiStd : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ n : Fin a.n,
   GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg ((a.G n).s + 1)) (GlobalTheory.Fam.TopLoc.xiStd a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ht n
  have hid := ((ha.tie (fun t => (nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g ht.pinX.std t).some) fun t => (nonempty_colCh (D := I.rec7 l Z) u _).some).2.idem n).1
  obtain ⟨hs, hX, -⟩ := hW.tr.ok.spaces
  have hsd : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L := fun j hj => by
    have e : ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ :=
      Set.ext (ht.pinX.xs j hj).2.2
    have h1 := GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq ((I.rec7 l Z).sp.X j) hs _ (hX j)
    have h2 : GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j) = (a.g.x j).L := SetLike.coe_injective (h1.trans e.symm)
    rw [← h2]
    exact GlobalTheory.PlaceModel.isSelfDualC_latFrame _
  have hm : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, (a.G n).FX ((a.G n).s + 1) le_rfl, (a.G n).FM, _,
    (GlobalTheory.QTw.GeoInhab.int_dense (a.G n).q hid).2, hid,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom _ _ (a.G n).q (a.G n).unit _ _ _ _ _ _ _ _ (hsd _ (by omega)) (hsd _ hm.le)
      (ht.pinX.xs _ (by omega)).2.2 (ht.pinX.xs _ hm.le).2.2 ((a.G n).latX _ _) (a.G n).latM,
    GlobalTheory.LastTwoSteps.xiTop_mem_SB _ (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) (a.G n).S.cond (a.G n).unitVol (by simp) _,
    (a.G n).cg_top, fun _ => rfl⟩

end GlobalTheory.Fam.TopLocFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  first | exact @GlobalTheory.LevChr.lam_eq_inv_xi | exact GlobalTheory.LevChr.lam_eq_inv_xi | (intros; apply GlobalTheory.LevChr.lam_eq_inv_xi <;> assumption)
end

