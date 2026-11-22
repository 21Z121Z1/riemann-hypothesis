import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtExtDat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ExtDatTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

theorem half_of_half {e e' : AE D} (h1 : e * e' = e') {x : Mx D m n} (hx : IsHalf e' x) : IsHalf e x := by
  intro i j
  rw [← hx i j, ← mul_assoc, h1]

theorem map_sub_half {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') {x : Mx D m n} (hx : IsHalf e' x) :
    x.map ((e - e') * ·) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [sub_mul, half_of_half h1 hx i j, hx i j, sub_self]

theorem map_half {e' : AE D} {x : Mx D m n} (hx : IsHalf e' x) : x.map (e' * ·) = x := by
  ext i j
  simp only [Matrix.map_apply]
  exact hx i j

theorem map_sub_eq {e e' : AE D} {u : Mx D m n} (hu : IsHalf e u) :
    u.map ((e - e') * ·) = u - u.map (e' * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, sub_mul, hu i j]

theorem half_add_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) : IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h' := h i j
    rw [Matrix.add_apply, mul_add, hx i j] at h'
    exact add_right_cancel h'
  · intro h i j
    rw [Matrix.add_apply, mul_add, h i j, hx i j]

theorem map_add_mul (a : AE D) (t x : Mx D m n) : (t + x).map (a * ·) = t.map (a * ·) + x.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, mul_add]

theorem mul_nsmul_comm' (a x : AE D) (k : ℕ) : a * (k • x) = k • (a * x) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]

theorem map_add_nsmul (a : AE D) (t u : Mx D m n) (k : ℕ) :
    (t + k • u).map (a * ·) = t.map (a * ·) + k • u.map (a * ·) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, mul_add, mul_nsmul_comm']

theorem half_map_self {e' : AE D} (h2 : e' * e' = e') (t : Mx D m n) : IsHalf e' (t.map (e' * ·)) := by
  intro i j
  simp only [Matrix.map_apply]
  rw [← mul_assoc, h2]

def extL (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun φ := GlobalTheory.ChainCol.extDat e e' Λ φ
  map_add' φ φ' := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c φ := by
    funext t
    simp only [GlobalTheory.ChainCol.extDat, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extL_apply (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) :
    extL e e' Λ φ = GlobalTheory.ChainCol.extDat e e' Λ φ := rfl

open Classical in
theorem extDat_trans {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (Φ : Mx D m n → ℂ) {x : Mx D m n} (hx : IsHalf e' x) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => Φ (t + x)) = fun t => GlobalTheory.ChainCol.extDat e e' Λ Φ (t + x) := by
  funext t
  have hxe : IsHalf e x := half_of_half h1 hx
  simp only [GlobalTheory.ChainCol.extDat, half_add_iff hxe, map_add_mul, map_sub_half h1 h2 hx, add_zero, map_half hx]

theorem extDat_sb {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf e' Λ Φ) :
    IsSBHalf e Λ (GlobalTheory.ChainCol.extDat e e' Λ Φ) := by
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨-, k, hk, hper, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hn
    apply ht
    simp only [GlobalTheory.ChainCol.extDat]
    exact if_neg fun hc => hn hc.1
  · have hku : IsHalf e (k • u) := fun i j => by rw [Matrix.smul_apply, mul_nsmul_comm', hue i j]
    have hsu : u.map ((e - e') * ·) ∈ Λ := by
      rw [map_sub_eq hue]
      exact sub_mem hu (hstab u hu)
    have hmem : (t + k • u).map ((e - e') * ·) ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ := by
      rw [map_add_nsmul]
      exact add_mem_cancel_right (nsmul_mem hsu k)
    have hval : Φ ((t + k • u).map (e' * ·)) = Φ (t.map (e' * ·)) := by
      rw [map_add_nsmul]
      exact hper _ (hstab u hu) (half_map_self h2 u) _
    simp only [GlobalTheory.ChainCol.extDat, half_add_iff hku, hmem, hval]
  · have hc : IsHalf e t ∧ t.map ((e - e') * ·) ∈ Λ := by
      by_contra hn
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      exact if_neg hn
    have hΦt : Φ (t.map (e' * ·)) ≠ 0 := by
      intro h0
      apply ht
      simp only [GlobalTheory.ChainCol.extDat]
      rw [if_pos hc, h0]
    have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq hc.1]
      abel
    rw [hsplit, nsmul_add]
    exact add_mem (hlat _ hΦt) (nsmul_mem hc.2 k)

theorem symplO_map_eq {S T : HSp D} {e e' : AE D} (h1 : e * e' = e') (h2 : e' * e' = e')
    {t y : WO S T} (ht : IsHalf e t) (hy : IsHalf (cA D e') y) :
    symplO S T (t.map (e' * ·)) y = symplO S T t y := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hyc : cA D (y c b) = e' * cA D (y c b) := by
    conv_lhs => rw [← hy c b]
    rw [map_mul, Formalism.IndefR.Fin.cA_cA]
  rw [Matrix.map_apply]
  calc _ = incA D ((HSpace.gram S)⁻¹ a b) * (e' * cA D (y c b)) * incA D (HSpace.gram T c d) * t d a := by ring
    _ = _ := by rw [← hyc]

open Classical in
theorem extDat_modul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) {e e' : AE D} (h1 : e * e' = e')
    (h2 : e' * e' = e') (Λ : AddSubgroup (WO S T)) (Φ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D e') y) :
    GlobalTheory.ChainCol.extDat e e' Λ (fun t => ψ (symplO S T t y) * Φ t) =
      fun t => ψ (symplO S T t y) * GlobalTheory.ChainCol.extDat e e' Λ Φ t := by
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  split_ifs with hc
  · rw [symplO_map_eq h1 h2 hc.1 hy]
  · rw [mul_zero]

open Classical in
theorem extDat_halfInd {e e' : AE D} (h2 : e' * e' = e') (Λ : AddSubgroup (Mx D m n))
    (hstab : ∀ u ∈ Λ, u.map (e' * ·) ∈ Λ) :
    GlobalTheory.ChainCol.extDat e e' Λ ((1 : ℂ) • halfInd e' Λ) = (1 : ℂ) • halfInd e Λ := by
  unfold halfInd
  rw [one_smul, one_smul]
  funext t
  simp only [GlobalTheory.ChainCol.extDat]
  by_cases ht : IsHalf e t
  · have hsplit : t = t.map (e' * ·) + t.map ((e - e') * ·) := by
      rw [map_sub_eq ht]
      abel
    have hiff : t ∈ Λ ↔ t.map ((e - e') * ·) ∈ Λ ∧ t.map (e' * ·) ∈ Λ := by
      constructor
      · intro h
        refine ⟨?_, hstab t h⟩
        rw [map_sub_eq ht]
        exact sub_mem h (hstab t h)
      · rintro ⟨ha, hb⟩
        rw [hsplit]
        exact add_mem hb ha
    by_cases hA : t.map ((e - e') * ·) ∈ Λ <;> by_cases hB : t.map (e' * ·) ∈ Λ <;>
      simp [ht, hA, hB, hiff, half_map_self h2 t]
  · simp [ht]

theorem isThetaAt_extDat : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ φ f : WO S T → ℂ} {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P → IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T ΛS ΛT fun _ => True) 1 f₀ φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (extDat e e' (latO S T ΛS ΛT fun _ => True) φ) f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ φ f e e' P P' hS hT hV he he' hP h
  unfold IsThetaAt at h ⊢
  obtain ⟨-, hall⟩ := h
  obtain ⟨hstd, hvac⟩ := hV
  have h1 : e * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he hP
  have h2 : e' * e' = e' := GlobalTheory.Tow.idemSum_mul_of_subset he' he' (Finset.Subset.refl _)
  have hstab : ∀ u ∈ (latO S T ↑ΛS ↑ΛT fun _ => True),
      u.map (e' * ·) ∈ (latO S T ↑ΛS ↑ΛT fun _ => True) := by
    intro u hu
    have hsm : u.map (e' * ·) = e' • u := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul]
    rw [hsm]
    exact GlobalTheory.PlaceModelSum.idem_smul_latO h2 hu
  have hce : cA D e * cA D e' = cA D e' := by
    rw [← map_mul (cA D), h1]
  refine ⟨?_, fun Tm hTm => ?_⟩
  · have hlv : IsLatVac (heisO ψ S T) (latO S T ↑ΛS ↑ΛT fun _ => True) f₀ := hvac.lat
    have hec : e * cA D e = 0 := by
      unfold IsIdemSum at he
      exact he.2
    exact GlobalTheory.PlaceModelSum.IsOrthSum.exists_model hstd hS hT
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he) hec hlv
  · have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e' (latO S T ↑ΛS ↑ΛT fun _ => True) 1 f₀
        (Tm ∘ₗ extL e e' (latO S T ↑ΛS ↑ΛT fun _ => True)) := by
      obtain ⟨htr, hmo, hva⟩ := hTm
      refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_trans h1 h2 _ Φ hx]
        exact htr _ (extDat_sb h1 h2 _ hstab hΦ) x (half_of_half h1 hx)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_modul ψ h1 h2 _ Φ hy]
        exact hmo _ (extDat_sb h1 h2 _ hstab hΦ) y (half_of_half hce hy)
      · simp only [LinearMap.comp_apply, extL_apply]
        rw [extDat_halfInd h2 _ hstab]
        exact hva
    rw [hall _ hT', LinearMap.comp_apply, extL_apply]

end GlobalTheory.ExtDatTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.KerDSub

open Filter GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem polMatch_mem_algD (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') {Φ Φ'}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') : Φ' ∈ algD G.M' B.ψ B.emb := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, φ' j, (hf' j).1, (hf' j).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
    by_contra h'
    exact hv ((hf' j).2.2 v h'))

theorem polMatch_zero_pure (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a')
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (hf : f ∈ G.M'.Pol B.ψ B.emb)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hv : ∀ᶠ v in cofinite, φ v = G.M'.vac v) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hz : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), S ⊆ T →
      R.p' f ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ v)) = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  have hfin := Filter.eventually_cofinite.mp hv
  refine ⟨X.T ∪ S ∪ hfin.toFinset, fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx), 0, 1,
    Fin.elim0, Fin.elim0, fun _ => f, fun _ => φ, fun i => i.elim0, fun _ => ⟨hf, hφ, fun v hv' => ?_⟩, ?_, ?_, ?_⟩
  · by_contra h'
    exact hv' (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h'))
  · simp
  · simp
  · rw [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one, hz _ fun x hx =>
      Finset.mem_union_left _ (Finset.mem_union_right _ hx)]

theorem polMatch_kInf (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (hMt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf)
    (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) (Φ Φ')
    (hPM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
  obtain ⟨A', hA'⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM'
    hMt.triple.weil' k hk
  have hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A f) φ := fun f φ h1 h2 =>
    hA f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) f)
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A' f) φ := fun f φ h1 h2 =>
    hA' f _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ φ h1 ((h2.and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) f)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hP
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ A ∘ₗ P.subtype
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.cpt k hk x.1 x.2 0 (zero_mem _) (A x.1) (A' 0) (hA x.1) (hA' 0)
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (A x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (A' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.cpt k hk y hy x hx (A y) (A' x) (hA y) (hA' x) hyx
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  refine ⟨T, hT, m, m', fun i => A (f i), φ, fun j => A' (f' j), φ',
    fun i => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
      (f i) (hf i).1 (A (f i)) (hA (f i)), (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM' hMt.triple.weil' k hk
      (f' j) (hf' j).1 (A' (f' j)) (hA' (f' j)), (hf' j).2.1, (hf' j).2.2⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure (f i) (φ i) (hf i).2.1 (hcof _ _ (hf i).2.2)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hpure' (f' j) (φ' j) (hf' j).2.1 (hcof _ _ (hf' j).2.2)
  · have := congrArg (LinearMap.rTensor _ L) heq
    simp only [map_sum, LinearMap.rTensor_tmul] at this
    simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this

theorem pure_sub {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

theorem kerD_isThetaSubG : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM
  obtain ⟨h0, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hM.fin
  let N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by simpa using hlin 0 0 x y 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h0⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by simpa using hlin 0 0 0 x c h0 hx.2⟩ }
  have hN : ∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := fun _ => Iff.rfl
  have hmem : ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ → Φ ∈ N := fun Φ h =>
    ⟨polMatch_mem_algD Bs Γ Xc R Rf h, h⟩
  have hpa : ∀ f φ, f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = Γ.M'.vac w) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := fun f φ hf hφ hv =>
    Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  obtain ⟨Φp, hΦp, hnot⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero_by_localMaps Bs Γ Xc om om' R Rf hM
  refine ⟨N, hN, ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun e => hnot ((hN Φp).mp (e ▸ hΦp)).2⟩
  ·
    intro v f φ hf hφ hv hφv
    have hz : Rf.p' v (φ v) = 0 := hM.fin.inv' v hφv
    refine hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f hf φ hφ hv {v} fun T hT => ?_)
    rw [MultilinearMap.map_coord_zero _ (⟨v, hT (Finset.mem_singleton_self v)⟩ : T) hz, TensorProduct.tmul_zero]
  ·
    intro γ hγ f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' f₁ = 0 := hM.real.quot'.lie γ hγ f hf f₁ hact
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f₁ hf₁ φ hφ hv ∅ fun T _ => by rw [hz, TensorProduct.zero_tmul])
  ·
    intro k hk f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' (f₁ - f) = 0 := by rw [map_sub, hM.real.quot'.cpt k hk f hf f₁ hact, sub_self]
    rw [← pure_sub]
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf (f₁ - f) (sub_mem hf₁ hf) φ hφ hv ∅ fun T _ => by
      rw [hz, TensorProduct.zero_tmul])
  ·
    classical
    intro v h hh Φ hΦ
    obtain ⟨T, hXT, hOn⟩ := (GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 Φ).mp hΦ.2
    have hOn' : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (insert v T) 0 Φ := by
      by_cases hvT : v ∈ T
      · rwa [Finset.insert_eq_of_mem hvT]
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert F E σ Bs a a' Γ Xc R Rf v
          (hM.fin.sph v fun h' => hvT (hXT h')).1 T 0 Φ hOn
    have := GlobalTheory.T.matched_maps_local_identity hP F E σ Bs a a' Γ Xc om om' R Rf hM (insert v T) v (Finset.mem_insert_self v T) h hh 0 Φ hOn'
    rw [map_zero] at this
    exact hmem _ ((GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 _).mpr
      ⟨insert v T, hXT.trans (Finset.subset_insert v T), this⟩)
  ·
    intro γ hγ Φ hΦ Φ₁ _ hd
    refine hmem _ (GlobalTheory.T.matched_maps_orbit_identity hP Bs Γ Xc om om' R Rf hM γ hγ 0 Φ hΦ.2 0 Φ₁ (fun x => ?_) hd)
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const 0 (0 : ℂ)
  ·
    intro k hk Φ hΦ
    have := polMatch_kInf Bs Γ Xc om om' R Rf hM k hk 0 Φ hΦ.2
    rw [map_zero] at this
    exact hmem _ this

end GlobalTheory.KerDSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section
namespace GlobalTheory.OppositeEdges

theorem oppositePath_prod_mulSingle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ) :
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  intro hj κ hκ
  set g : Γ.VertexGroup := Pi.mulSingle (j + 1, Γ.m) κ with hg
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  have hK : ∀ Y, g Y ∈ GlobalTheory.SplitWeil.KO k _ := by
    intro Y
    by_cases hY : Y = (j + 1, Γ.m)
    · subst hY; simpa [hg] using hκ
    · rw [hg, Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z

  have hfar : ∀ b : Edge, b.src ≠ (j + 1, Γ.m) → b.tgt ≠ (j + 1, Γ.m) → Γ.edgeFactor .one g b = 1 := by
    intro b h1 h2
    simp [Grid.edgeFactor, hg, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, hap]
  have htheta : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one g)).prod = 1 := by
    refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  have hex : (((List.range Γ.m).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one g)).prod =
      ∏ i ∈ Finset.range Γ.m, Γ.edgeFactor .one g (.ex i Γ.m) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hne : j ≠ j + 1 := by omega
  have hrest : ∀ i ∈ Finset.range Γ.m, i ≠ j ∧ i ≠ j + 1 → Γ.edgeFactor .one g (.ex i Γ.m) = 1 := by
    intro i _ hi
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  rw [oppositePath, List.map_append, List.prod_append, htheta, mul_one, hex,
    Finset.prod_eq_mul j (j + 1) hne hrest (by simp; omega) (by simp; omega)]
  have hκa : ∀ z : ℂ, apow (gdet (Assignment.one.read κ)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO hκ)) z
  have hj1 : (j + 1 + 1, Γ.m) ≠ (j + 1, Γ.m) := by simp
  have hj0 : (j, Γ.m) ≠ (j + 1, Γ.m) := by simp
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, Pi.mulSingle_eq_of_ne hj1,
    Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_same, hκa, map_one, hap, Units.val_one, inv_one, one_mul]
  simp only [Grid.kappa, Grid.blockChar, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Nat.add_sub_cancel]
  have h1 := Units.ne_zero (Γ.chi (Γ.m - (j + 1)) (gdet κ))
  have h2 := Units.ne_zero (Γ.chi (Γ.m - j) (gdet κ))
  have h3 := Units.ne_zero ((Γ.eta ^ ((Γ.rank (j + 1, Γ.m) + 1) % 2)) (gdet κ))
  field_simp

end GlobalTheory.OppositeEdges
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaConvergenceAtScaleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_convergence_at_scale : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  first | exact @GlobalTheory.thetaConv_and_isAutFun_thetaChi_of_hidaSetting | exact GlobalTheory.thetaConv_and_isAutFun_thetaChi_of_hidaSetting | (intros; apply GlobalTheory.thetaConv_and_isAutFun_thetaChi_of_hidaSetting <;> assumption)
end

