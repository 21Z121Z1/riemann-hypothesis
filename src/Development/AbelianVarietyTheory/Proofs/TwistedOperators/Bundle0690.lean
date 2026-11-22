import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0673
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0095
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientProjection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesMultiplicity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PoinMult

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

open Classical in

theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hDS hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := GlobalTheory.T.poincare_series_cuspidal hDS D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end GlobalTheory.PoinMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ProdDatum

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Gen

variable {D : D7} {S T : HSp D}

def tens (a b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ :=
  fun y => if IsHalf (a + b) y then Φ (a • y) * Ψ (b • y) else 0

theorem half_iff {a : AE D} {y : WO S T} : IsHalf a y ↔ a • y = y :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem tens_comm (a b : AE D) (Φ Ψ : WO S T → ℂ) : tens a b Φ Ψ = tens b a Ψ Φ := by
  funext y
  unfold tens
  rw [add_comm b a, mul_comm]

def tensL (a b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := tens a b Φ
  map_add' Ψ Ψ' := by
    funext y
    simp only [tens, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Ψ := by
    funext y
    simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem half_add_iff {e : AE D} {u : WO S T} (hu : IsHalf e u) (t : WO S T) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [half_iff] at hu
  rw [half_iff, half_iff, smul_add, hu, add_left_inj]

theorem aux1 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (a : R) (k l : ℕ) (u : M) :
    a • ((k * l) • u) = k • (l • (a • u)) := by rw [smul_comm a, mul_smul]

theorem aux2 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (ha : a * a = a) (l : ℕ) (u : M) :
    a • (l • (a • u)) = l • (a • u) := by rw [smul_comm a l, smul_smul a, ha]

theorem aux3 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a b : R} (k l : ℕ) {t : M} (h : (a + b) • t = t) :
    (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := by
  rw [← mul_smul l k, ← mul_smul k l, mul_comm l k, ← smul_add, ← add_smul, h]

theorem aux4 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {a : R} (k : ℕ) {t : M} (h : a • t = t) :
    a • (k • t) = k • t := by rw [smul_comm, h]

variable {a b : AE D} {Λ : AddSubgroup (WO S T)}

theorem tens_sb (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ)
    {Φ Ψ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a + b) Λ (tens a b Φ Ψ) := by
  obtain ⟨-, k, hk, h2, h3⟩ := hΦ
  obtain ⟨-, l, hl, g2, g3⟩ := hΨ
  refine ⟨fun t ht => ?_, k * l, Nat.mul_pos hk hl, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hh' : IsHalf (a + b) ((k * l) • u) := half_iff.2 (aux4 _ (half_iff.1 hh))
    unfold tens
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h, if_pos ((half_add_iff hh' t).2 h), smul_add, smul_add]
      have e1 : a • ((k * l) • u) = k • (l • (a • u)) := aux1 a k l u
      have e2 : b • ((k * l) • u) = l • (k • (b • u)) := by rw [mul_comm k l]; exact aux1 b l k u
      rw [e1, e2, h2 _ (nsmul_mem (hΛa u hu) l) (half_iff.2 (aux2 ha l u)),
        g2 _ (nsmul_mem (hΛb u hu) k) (half_iff.2 (aux2 hb k u))]
    · rw [if_neg h, if_neg fun h' => h ((half_add_iff hh' t).1 h')]
  · unfold tens at ht
    by_cases h : IsHalf (a + b) t
    · rw [if_pos h] at ht
      have e : (k * l) • t = l • (k • (a • t)) + k • (l • (b • t)) := aux3 k l (half_iff.1 h)
      rw [e]
      exact add_mem (nsmul_mem (h3 _ (left_ne_zero_of_mul ht)) l) (nsmul_mem (g3 _ (right_ne_zero_of_mul ht)) k)
    · exact absurd (if_neg h) ht

theorem tens_ind (ha : a * a = a) (hb : b * b = b) (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens a b (halfInd a Λ) (halfInd b Λ) = halfInd (a + b) Λ := by
  funext y
  have h1 : IsHalf a (a • y) := half_iff.2 (by rw [smul_smul, ha])
  have h2 : IsHalf b (b • y) := half_iff.2 (by rw [smul_smul, hb])
  unfold tens halfInd
  by_cases h : IsHalf (a + b) y
  · rw [if_pos h]
    by_cases hy : y ∈ Λ
    · rw [if_pos ⟨hΛa y hy, h1⟩, if_pos ⟨hΛb y hy, h2⟩, if_pos ⟨hy, h⟩, one_mul]
    · rw [if_neg (fun h' : y ∈ Λ ∧ _ => hy h'.1)]
      by_cases hay : a • y ∈ Λ
      · have : b • y ∉ Λ := fun hby => hy (by
          have := add_mem hay hby
          rwa [← add_smul, half_iff.1 h] at this)
        rw [if_neg (fun h' : b • y ∈ Λ ∧ _ => this h'.1), mul_zero]
      · rw [if_neg (fun h' : a • y ∈ Λ ∧ _ => hay h'.1), zero_mul]
  · rw [if_neg h, if_neg (fun h' : y ∈ Λ ∧ _ => h h'.2)]

theorem tens_model (ψ : AddChar (AF D.host.F) ℂ) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hΛa : ∀ u ∈ Λ, a • u ∈ Λ) (hΛb : ∀ u ∈ Λ, b • u ∈ Λ) {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a Λ Φ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ 1 (Tm (tens a b Φ (halfInd b Λ))) (Tm ∘ₗ tensL a b Φ) := by
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, by rw [one_smul]; rfl⟩
  · have hx1 : b • x = x := half_iff.1 hx
    have hx0 : a • x = 0 := by rw [← hx1, smul_smul, hab, zero_smul]
    have hx2 : IsHalf (a + b) x := half_iff.2 (by rw [add_smul, hx0, hx1, zero_add])
    have e : tens a b Φ (fun t => Ψ (t + x)) = fun t => tens a b Φ Ψ (t + x) := by
      funext t
      simp only [tens, half_add_iff hx2 t, smul_add, hx0, hx1, add_zero]
    change Tm (tens a b Φ (fun t => Ψ (t + x))) = heisO ψ S T x (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.trans _ (tens_sb ha hb hΛa hΛb hΦ hΨ) x hx2
  · have hy1 : cA D b • y = y := half_iff.1 hy
    have hy2 : IsHalf (cA D (a + b)) y := half_iff.2 (by
      rw [RingHom.map_add, add_smul, hy1, ← hy1, smul_smul, ← RingHom.map_mul, hab, RingHom.map_zero, zero_smul, zero_add])
    have e : tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens a b Φ Ψ t := by
      funext t
      simp only [tens]
      rw [symplO_smul, hy1]
      split_ifs <;> ring
    change Tm (tens a b Φ (fun t => ψ (symplO S T t y) * Ψ t)) = heisO ψ S T y (Tm (tens a b Φ Ψ))
    rw [e]
    exact hT.modul _ (tens_sb ha hb hΛa hΛb hΦ hΨ) y hy2

end Gen

theorem orth_of_idemSum {D : D7} {a b : AE D} {P Q R : Finset (Pl D.host.E)} (ha : IsIdemSum a P) (hb : IsIdemSum b Q)
    (h : IsIdemSum (a + b) R) : a * b = 0 ∧ (a + cA D a) * (b + cA D b) = 0 := by
  have a2 := idemSum_mul_self ha
  have b2 := idemSum_mul_self hb
  have s2 := idemSum_mul_self h
  have hab : a * b = 0 := by
    have h2 : incA D 2⁻¹ * (1 + 1) = 1 := by
      rw [← (incA D).map_one, ← RingHom.map_add, ← RingHom.map_mul]
      congr 1
      norm_num
    linear_combination incA D 2⁻¹ * (s2 - a2 - b2) - a * b * h2
  have h1 := h.2
  rw [RingHom.map_add] at h1
  have ha' := ha.2
  have hb' := hb.2
  have k1 : a * cA D b = 0 := by
    linear_combination a * h1 - (cA D a + cA D b) * a2 - ha' - (cA D a + cA D b) * hab
  have k2 : b * cA D a = 0 := by
    linear_combination h1 - ha' - hb' - k1
  have k3 : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  exact ⟨hab, by linear_combination hab + k1 + k2 + k3⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

set_option maxHeartbeats 1000000 in

theorem exists_prod {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d₁ d₂ : FinDatum G t p) (c₁ c₂ : WO (G.pS p) (G.pT p) →₀ ℂ) (he : IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P))
    (h₁ : IsCombOf W d₁ c₁) (h₂ : IsCombOf W d₂ c₂) :
    ∃ (d : FinDatum G t p) (c : WO (G.pS p) (G.pT p) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf W d c ∧
      (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧
      ∀ f, comb W.ψ _ _ c f = comb W.ψ _ _ c₁ (comb W.ψ _ _ c₂ f) := by
  have a2 := idemSum_mul_self d₁.e_is
  have b2 := idemSum_mul_self d₂.e_is
  obtain ⟨hab, horth⟩ := orth_of_idemSum d₁.e_is d₂.e_is he
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True,
      a • u ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  have HC := GlobalTheory.HeisComb.main D W.ψ (G.pS p) (G.pT p)
  obtain ⟨c, hsupp, hc⟩ := HC.1 c₁ c₂
  let d : FinDatum G t p :=
    { P := d₁.P ∪ d₂.P
      P_over := fun w hw => (Finset.mem_union.1 hw).elim (d₁.P_over w) (d₂.P_over w)
      e := d₁.e + d₂.e
      e_is := he
      fn := tens d₁.e d₂.e d₁.fn d₂.fn
      sb := tens_sb a2 b2 (hsm _ a2) (hsm _ b2) d₁.sb d₂.sb
      z := 1
      z_cen := (FinDatum.vacuum G t p).z_cen
      z_supp := (FinDatum.vacuum G t p).z_supp }
  refine ⟨d, c, rfl, rfl, ⟨fun u hu => ?_, fun u hu => ?_, fun f₀ hth hvac => ⟨?_, fun Tm hTm => ?_⟩⟩,
    fun y hy => if_pos hy, hc⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    rw [Matrix.map_add _ (fun a b => RingHom.map_add _ a b), h₁.1 x hx, h₂.1 y hy, add_zero]
  · obtain ⟨x, hx, y, hy, rfl⟩ := hsupp u hu
    intro i j
    have k1 := h₁.2.1 x hx i j
    have k2 := h₂.2.1 y hy i j
    change (d₁.e + d₂.e + cA D (d₁.e + d₂.e)) * (x i j + y i j) = x i j + y i j
    rw [RingHom.map_add]
    linear_combination (1 - d₂.e - cA D d₂.e) * k1 + (1 - d₁.e - cA D d₁.e) * k2 + (x i j + y i j) * horth
  · exact (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1
  · obtain ⟨c', k1, k2⟩ := GlobalTheory.CombsExist.exists_comb_model W.ψ _ _ _ _ d₂.e d₂.fn W.ψ_std hS hT b2 d₂.e_is.2
      (infPart_idemSum d₂.e_is) d₂.sb
    have hT1 : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) (d₁.e + d₂.e)
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ Tm := hTm
    have hT2 := hT1
    rw [add_comm] at hT2
    have v := hT1.vac
    rw [one_smul] at v
    have m2 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 (GlobalTheory.isSBHalf_halfInd d₁.e _)
    rw [tens_ind a2 b2 (hsm _ a2) (hsm _ b2), v] at m2
    have m1 := tens_model W.ψ b2 a2 (by rw [mul_comm, hab]) (hsm _ b2) (hsm _ a2) hT2 (GlobalTheory.isSBHalf_halfInd d₂.e _)
    rw [tens_ind b2 a2 (hsm _ b2) (hsm _ a2), add_comm, v] at m1
    have m3 := tens_model W.ψ a2 b2 hab (hsm _ a2) (hsm _ b2) hT1 d₁.sb
    have e2 : comb W.ψ _ _ c₂ f₀ = comb W.ψ _ _ c' f₀ := ((h₂.2.2 f₀ hth hvac).2 _ m2).trans (k2 f₀ _ m2).symm
    have e1 := (h₁.2.2 f₀ hth hvac).2 _ m1
    have e3 := k2 _ _ m3
    have hcomm := HC.2.1 c₁ c' (fun x hx y hy => HC.2.2.2 _ _ x y
      (by rw [RingHom.map_add, Formalism.L2.Theta.cA_cA, add_comm]) horth (h₁.2.1 x hx) (k1 y hy).2) f₀
    rw [hc, e2, hcomm, e1]
    refine Eq.trans ?_ e3
    congr 1
    exact congrArg Tm (tens_comm _ _ _ _)

theorem prod_datum : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t j d₁ d₂ c₁ c₂ =>
    exists_prod ch.W (p := .top t j) (ch.G.isV (X := .top j) j.2.le fun _ h => by cases h).sd
      (ch.G.isV (X := .top (j + 1)) j.2 fun _ h => by cases h).sd d₁ d₂ c₁ c₂⟩⟩

end GlobalTheory.ProdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.RealAsm

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_Jm' (ε : Fin m → Bool) : IsUnit (Jm ε) := by
  refine IsUnit.of_mul_eq_one (Jm ε) ?_
  simp only [Jm, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem umat_mem (ε : Fin m → Bool) (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem one_mem (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := (1 : UJ ε).2

theorem continuous_umat (ε : Fin m → Bool) : Continuous (fun g : UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem smV_translate {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Mat m → (H →L[ℂ] H)} (hπ : IsDS ε lam π) {g : Mat m}
    (hg : g ∈ UJset ε) {v : H} (hv : SmV (lieOf (Jm ε)) π v) : SmV (lieOf (Jm ε)) π (π g v) :=
  GlobalTheory.SmLinSub.rep_mem (isUnit_Jm' ε) hπ.2.2.1 hv hg

theorem smV_const_smul {L : Set (Mat m)} {π : Mat m → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : SmV L π v) : SmV L π (a • v) :=
  fun k Xs hX => by simpa only [map_smul] using (hv k Xs hX).const_smul a

theorem integrable_low_coef (hD : DecPow) (hI : PowInt) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (B : ℝ) (hn : 3 ≤ n)
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (1000 * (n : ℝ) ^ 3)) (hB : ∀ a, |lam a| ≤ B)
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    Integrable (fun h : UJ ε => ⟪w, σ (umat h) w⟫_ℂ) (muG ε) := by
  have hdec := hD n ε lam B hn hl hg hB H σ hσ w hw
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA : 4 * (n : ℝ) ^ 2 + 1 ≤ 40 * (n : ℝ) ^ 2 := by nlinarith
  have hpow := (hI n ε (40 * (n : ℝ) ^ 2) (by omega) hA).1
  refine (hpow.const_mul (Real.exp (100 * (n : ℝ) ^ 3))).mono' ?_ (Filter.Eventually.of_forall fun h => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.inner ((hσ.2.2.1.2.2 w).comp_continuous (continuous_umat ε) (umat_mem ε))
  · exact hdec _ (umat_mem ε h)

theorem big_mul (a b : ℝ) (n : ℕ) (B : ℝ) : big a n B * big b n B = big (a + b) n B := by
  unfold big
  rw [← Real.exp_add]
  ring_nf

theorem big_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : big a n B ≤ big b n B := by
  unfold big
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith)
  have h2 : 0 ≤ ((n : ℝ) + 1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_right hab h2
  exact mul_le_mul_of_nonneg_right this h1

theorem big_pos (a : ℝ) (n : ℕ) (B : ℝ) : 0 < big a n B := Real.exp_pos _

theorem one_le_B {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {B : ℝ} (hP : Par e ε lam ε' mu B) : 1 ≤ B := by
  have hn := hP.three_le
  have h := hP.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h0 := abs_le.1 (hP.bound.1 ⟨0, by omega⟩)
  have h1 := abs_le.1 (hP.bound.1 ⟨1, by omega⟩)
  linarith [h0.1, h0.2, h1.1, h1.2]

theorem gap_mono {k : ℕ} {ε : Fin k → Bool} {lam : Fin k → ℝ} {a b : ℝ} (hab : a ≤ b) (h : GapAtLeast ε lam b) :
    GapAtLeast ε lam a := fun x y hxy => hab.trans (h x y hxy)

end GlobalTheory.SepReal.RealAsm

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.RealAsm

end GlobalTheory.SepReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth : Big fun ch => GrpAt ch := by
  first | exact @GlobalTheory.RowGrpSplit.grpAt_big | exact GlobalTheory.RowGrpSplit.grpAt_big | (intros; apply GlobalTheory.RowGrpSplit.grpAt_big <;> assumption)
end

