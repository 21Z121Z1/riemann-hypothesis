import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0744
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0741
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0723
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepth
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem wtAt_big : Big fun ch => ∀ s, WtAt ch s := by
  refine GlobalTheory.RowReal.big_mono ?_ (GlobalTheory.T.rowTest_tupleTerm_measures_differ_by_scalars.and GlobalTheory.T.unfolding_cell_mass_eq_const_mul_local_coefficients)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH
  obtain ⟨hA, hC⟩ := h
  have hc := hC s ρ μ hH
  classical
  let cf : ℕ → ℂ := fun j => if hj : j ∈ idx D then (hc j hj).choose else 1
  refine ⟨((idx D).map cf).prod, fun t Φ β b hb M M' hM hM' => ?_⟩
  obtain ⟨x, hx, hx1⟩ := hA t Φ β M M' hM hM'
  refine ⟨x, hx, ?_⟩
  have hlt : ∀ j ∈ idx D, 1 ≤ j ∧ j + 2 ≤ D.R.m := fun j hj => by
    rw [idx, List.mem_range'_1] at hj; omega
  have hgf : ∀ j ∈ idx D, b j ∈ GfC _ := fun j hj => by
    obtain ⟨δ, r, -, -, hf⟩ := hb.2 j hj (by have := hlt j hj; omega)
    exact hf.1
  have hfac : ∀ j ∈ idx D, (if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩ else 0) *
      ((x (.top j) : ℝ) : ℂ) = cf j * (colCoef ch t β j : ℂ) := fun j hj => by
    rw [dif_pos (hgf j hj)]
    have hs := hx (.top j) (show j ≤ D.R.m by have := hlt j hj; omega) (by simp only [ne_eq, Node.top.injEq]; have := hlt j hj; omega)
    have e := (hc j hj).choose_spec t Φ β b hb M M' hM hM' (x (.top j)) hs (hgf j hj)
    simp only [cf, dif_pos hj]
    exact e
  have hsP : sProd D x = ((idx D).map fun j => ((x (.top j) : ℝ) : ℂ)).prod := by
    have h2 : ∏ i ∈ Finset.range (D.R.m + 1), ((x (.grid i D.R.m) : ℝ) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [hx1 (.grid i D.R.m) ⟨by simp at hi; omega, rfl⟩ (by simp) (fun j _ => by simp)]
      simp
    rw [sProd, h2, mul_one, ← List.prod_toFinset _ (show (idx D).Nodup from List.nodup_range')]
    symm
    refine Finset.prod_subset (fun j hj => ?_) (fun j hj0 hj => ?_)
    · rw [List.mem_toFinset] at hj
      have := hlt j hj
      exact Finset.mem_range.2 (by omega)
    · rw [List.mem_toFinset] at hj
      have hj1 := Finset.mem_range.1 hj0
      rw [hx1 (.top j) (show j ≤ D.R.m by omega) (by simp only [ne_eq, Node.top.injEq]; omega) (fun j' hj' e => by cases e; exact hj hj')]
      simp
  have hwt : GlobalTheory.RowVal.wt ρ μ b = ((idx D).map fun j => if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩
      else 0).prod := by
    unfold GlobalTheory.RowVal.wt
    congr 1
  rw [hwt, hsP, ← List.prod_map_mul, List.map_congr_left hfac, List.prod_map_mul, coef_prod]

end GlobalTheory.RowWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem isHalf_smul {e : AE D} {u : WO S T} (hu : IsHalf e u) (z : AE D) : IsHalf e (z • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm, hu i j]

theorem isHalf_add {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_sub {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem isHalf_idem {e : AE D} (he : e * e = e) (u : WO S T) : IsHalf e (e • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem mxAt_of_isHalf {e : AE D} (hinf : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) : MxAt (fun _ => True) u :=
  fun i j => by
    refine Ideal.mem_inf.2 ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, ← hu i j, map_mul, hinf, zero_mul]
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      exact absurd trivial w.2

theorem cosInd_add {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {u : WO S T} (hu : IsHalf e u)
    (hm : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) (t : WO S T) : cosInd e κ (t + u) = cosInd e κ t := by
  have key : ∀ (t v : WO S T), IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → t ∈ cosSet e κ → t + v ∈ cosSet e κ := by
    rintro t v hv hvm ⟨ht, x₀, hx₀, hd⟩
    refine ⟨isHalf_add ht hv, x₀, hx₀, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hd hvm
  unfold cosInd
  by_cases h : t ∈ cosSet e κ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key t u hu hm h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have hn : IsHalf e (-u) := fun i j => by simp only [Matrix.neg_apply, mul_neg, hu i j]
    simpa using key (t + u) (-u) hn (neg_mem hm) h'

variable {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}

theorem heisO_fix_trans (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {u : WO S T}
    (hu : IsHalf e u) (hinv : ∀ t, Φ (t + u) = Φ t) : heisO ψ S T u f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.trans Φ hΦ u hu]
  congr 1
  funext t
  exact hinv t

theorem heisO_fix_modul (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {y : WO S T}
    (hy : IsHalf (cA D e) y) (hinv : ∀ t, Φ t ≠ 0 → ψ (symplO S T t y) = 1) : heisO ψ S T y f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.modul Φ hΦ y hy]
  congr 1
  funext t
  by_cases h0 : Φ t = 0
  · rw [h0, mul_zero]
  · rw [hinv t h0, one_mul]

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ}

theorem isLatVac_of_cos (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (κ : Cos ΛS ΛT 𝔪) (hcos : ∀ t ∈ cosSet e κ, t ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
    {f₀ f : WO S T → ℂ} (hf₀ : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) f₀)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ (cosInd e κ) f)
    {Γ : AddSubgroup (WO S T)}
    (hΓ : ∀ u ∈ Γ, u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ∧ e • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) :
    IsLatVac (heisO ψ S T) Γ f := by
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have e2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, e1]
  have c2 : cA D e * e = 0 := by rw [mul_comm, e2]
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT h𝔪 e1 hinf κ
  have ann : ∀ x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), MxAt (fun _ => True) x →
      ∀ y ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), ψ (symplO S T x y) = 1 := fun x hx hx' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T ΛS ΛT hS hT (fun _ => True) x hx').1 hx

  have hA : ∀ v, IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → heisO ψ S T v f = f := fun v hv hm =>
    heisO_fix_trans h hSB hv (cosInd_add κ hv hm)

  have hB : ∀ v, IsHalf (cA D e) v → v ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → heisO ψ S T v f = f :=
    fun v hv hm => heisO_fix_modul h hSB hv fun t ht => by
      have htc : t ∈ cosSet e κ := Set.mem_of_indicator_ne_zero ht
      exact ann t (hcos t htc) (mxAt_of_isHalf hinf htc.1) v hm

  have hC : ∀ r : WO S T, (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T r f₀ = f₀ → heisO ψ S T r f = f :=
    fun r hr h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ _ f h r hr h0
  have hoff : ∀ u : WO S T, ∀ i j, e * (u - e • u - cA D e • u) i j = 0 ∧ cA D e * (u - e • u - cA D e • u) i j = 0 :=
    fun u i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      constructor
      · linear_combination (-(u i j)) * e1 + (-(u i j)) * e2
      · linear_combination (-(u i j)) * c2 + (-(u i j)) * c1
  have hdec : ∀ u : WO S T, u = e • u + (cA D e • u + (u - e • u - cA D e • u)) := fun u => by abel

  have dbl : ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → IsHalf (cA D e) b →
      b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T (2 • (a + (b + r))) f = f := by
    intro a b r hae ham hal hbe hbl hrl hr0
    have h2 : 2 • (a + (b + r)) = (a + a) + (b + b + (r + r)) := by rw [two_nsmul]; abel
    have hph : ψ (symplOH S T (a + a) (b + b + (r + r))) = 1 := by
      rw [GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
      exact ann a hal (mxAt_of_isHalf hinf hae) _ (add_mem (add_mem hbl hbl) (add_mem hrl hrl))
    have hbr : symplO S T (b + b) (r + r) = 0 := GlobalTheory.Hk3.symplO_half_off S T (isHalf_add hbe hbe) fun i j => by
      rw [GlobalTheory.DualPairCheck.cA_cA, Matrix.add_apply, mul_add, (hr0 i j).1, add_zero]
    have hrr : heisO ψ S T (r + r) f = f := hC _ (fun i j => by
        simp only [Matrix.add_apply, mul_add, (hr0 i j).1, (hr0 i j).2, add_zero, and_self])
      (by rw [← two_nsmul]; exact hf₀.1 r hrl)
    have hbb : heisO ψ S T (b + b) f = f := hB _ (isHalf_add hbe hbe) (add_mem hbl hbl)
    have haa : heisO ψ S T (a + a) f = f := hA _ (isHalf_add hae hae) (add_mem ham ham)
    have key := GlobalTheory.SplitScalar.heisO_heisO ψ S T (a + a) (b + b + (r + r)) f
    rw [hph, one_smul, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hbr, hrr, hbb, haa] at key
    rw [h2, ← key]

  have sng : ∀ e' : AE D, IsSplitIdem D e' → ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      IsHalf (cA D e) b → b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) →
      IsHalf e' a → IsHalf e' b → IsHalf e' r → heisO ψ S T (a + (b + r)) f = f := by
    intro e' he' a b r hae ham hbe hbl hrl hr0 ha' hb' hr'
    have horth : ∀ x y : WO S T, IsHalf e' x → IsHalf e' y → symplO S T x y = 0 := fun x y hx hy =>
      GlobalTheory.Hk3.symplO_half_off S T hx fun i j => by
        rw [← hy i j, ← mul_assoc, mul_comm (cA D e'), he'.2.1, zero_mul]
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ ha' (isHalf_add hb' hr')),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ hb' hr'), hC r hr0 (hf₀.2 e' he' r hrl hr'),
      hB b hbe hbl, hA a hae ham]
  refine ⟨fun u hu => ?_, fun e' he' u hu hu' => ?_⟩
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    rw [hdec u]
    exact dbl _ _ _ (isHalf_idem e1 u) hu2 ha (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    have hae : IsHalf e' (e • u) := isHalf_smul hu' e
    have hbe : IsHalf e' (cA D e • u) := isHalf_smul hu' _
    rw [hdec u]
    exact sng e' he' _ _ _ (isHalf_idem e1 u) hu2 (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
      hae hbe (isHalf_sub (isHalf_sub hu' hae) hbe)

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

theorem cosInd_ne_zero {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos Λ Λ' 𝔪) : cosInd e κ ≠ 0 := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  intro h0
  have hmem : e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ cosSet e (Submodule.Quotient.mk x₀ : Cos Λ Λ' 𝔪) :=
    ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he], x₀, rfl, by rw [sub_self]; exact zero_mem _⟩
  have := congrFun h0 (e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D))
  unfold cosInd at this
  rw [Set.indicator_of_mem hmem] at this
  exact one_ne_zero this

end GlobalTheory.CosDep

theorem GlobalTheory.CosDep.cosVec_dep : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ Dep W (.chi i 0) (W.cosVec i κ) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ) := by
  intro D hoff T L μ₀ hL sc G W M _ i hi κ
  obtain ⟨e, he, hcos⟩ := W.cosVec_is
  have h := hcos i hi κ
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hv := (W.vac_is i hi).2
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (G.pl.modul_ne_bot sc) e1 hinf κ
  refine ⟨?_, ⟨GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ, ?_⟩, fun τ => ?_⟩
  · obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
    rw [hall Tm hTm]
    have hne : W.vac i ≠ 0 := by
      rintro h0
      obtain ⟨⟨p, hp⟩, hall'⟩ := hv.norm
      have := hall' p hp
      rw [h0] at this
      simp [nrm2] at this
    exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ _ _ _ _ e _ _ Tm W.ψ_std hS hT e1 he.2 hinf hTm hne hSB
      (GlobalTheory.CosDep.cosInd_ne_zero e1 κ)
  · exact GlobalTheory.CosDep.isLatVac_of_cos W.ψ_std hS hT he (G.pl.modul_ne_bot sc) κ
      (fun t ht => GlobalTheory.T.mem_completedHomLattice_of_mem_latticeHomCoset hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hoff hL G) κ ht) hv.lat h fun u hu => ⟨hu.1, hu.2 e he⟩
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is hinf
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj.infPart_eq h hv.theta
      (GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ) (hv.fock τ)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormApproxMultiplicityMaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspPureApprox

theorem exists_sum_approx : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨ψ, hψ, hK, hle⟩ := GlobalTheory.T.cusp_form_approx_K_finite_type hP D G₀ Pl0 T A Ks R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨n, Tm, v, hT, heq⟩ := GlobalTheory.T.cusp_form_finite_dim_invariant hP D G₀ Pl0 T A Ks R G hR hG i j hi hj ψ hψ hK
  exact ⟨n, Tm, v, hT, fun g => by rw [← heq g]; exact hle g⟩

end GlobalTheory.CuspPureApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowSmulMemSelfDualModulusShiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_smul_mem_selfDualModulusShift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  first | exact @GlobalTheory.DepHalf.smul_mem_latBig | exact GlobalTheory.DepHalf.smul_mem_latBig | (intros; apply GlobalTheory.DepHalf.smul_mem_latBig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (e : AE D),
    IsIdemSum e (locPl G t) →
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  first | exact @GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | exact GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | (intros; apply GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.EntireJetUniq

open Formalism.L2.KerInert.PullbackComparison in

theorem eq_of_applyAt0_monomial_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  intro D N N' Φ Ψ hΦ hΨ h
  classical
  have aΦ := GlobalTheory.analyticOnNhd_of_differentiable_vc Φ hΦ
  have aΨ := GlobalTheory.analyticOnNhd_of_differentiable_vc Ψ hΨ
  have hmono : ∀ (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ),
      Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G =
        (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
    intro k G
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl, one_mul]
  have ht : ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D Φ α = Formalism.MainNotions.TaylorLogMetric.taylor D Ψ α := by
    intro α
    have h1 := h α
    rw [hmono, hmono] at h1
    have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact mul_left_cancel₀ hne h1
  have hd : ∀ (n : ℕ) (z : Formalism.MainNotions.TaylorLogMetric.VC D N N'),
      iteratedFDeriv ℂ n Φ 0 (fun _ => z) = iteratedFDeriv ℂ n Ψ 0 (fun _ => z) := by
    intro n z
    rw [iter_expand, iter_expand]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [iter_eq_taylor D Φ aΦ κ (ak D κ) (toMultiset_ak D κ).symm,
      iter_eq_taylor D Ψ aΨ κ (ak D κ) (toMultiset_ak D κ).symm, ht]
  obtain ⟨p, r, hp⟩ := aΦ 0 (Set.mem_univ _)
  obtain ⟨q, s, hq⟩ := aΨ 0 (Set.mem_univ _)
  refine aΦ.eq_of_eventuallyEq aΨ (z₀ := 0) ?_
  have hball : Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') (min r s) ∈ nhds 0 :=
    Metric.eball_mem_nhds 0 (lt_min hp.r_pos hq.r_pos)
  filter_upwards [hball] with y hy
  have hy1 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') r :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') s :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have s1 := hp.hasSum_iteratedFDeriv hy1
  have s2 := hq.hasSum_iteratedFDeriv hy2
  simp only [zero_add] at s1 s2
  simp only [hd] at s1
  exact s1.unique s2

end GlobalTheory.EntireJetUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PieceA

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (M : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem finLat_comap_extX {V V₀ W : HSp D} {ρ : ℕ} (d : GlobalTheory.MixModel.HypDec V V₀ ρ) {Γ : AddSubgroup (WO V W)}
    (hΓ : FinLat Γ) : FinLat (Γ.comap (d.extX W)) := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have hc : Continuous (d.extX W) := by
    show Continuous fun a : Mx D W.rank ρ => a ⬝ d.pX
    exact continuous_id.matrix_mul continuous_const
  have hinv : ∀ a : Mx D W.rank ρ, d.extX W a ⬝ d.jX = a := fun a => by
    rw [GlobalTheory.MixModel.HypDec.extX_apply, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jX, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hinv a]
    exact mxAt_mul_right (hΓ.fin _ ha) _
  · have hK : IsCompact ((fun w : WO V W => w ⬝ d.jX) '' (Γ : Set (WO V W))) :=
      hΓ.cpt.image (continuous_id.matrix_mul continuous_const)
    refine hK.of_isClosed_subset (hΓ.cpt.isClosed.preimage hc) ?_
    intro a ha
    exact ⟨_, ha, hinv a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hΓ.opn
    refine ⟨d.extX W ⁻¹' U, hU.preimage hc, by simpa using h0, fun a ha haf => ?_⟩
    exact hUA _ ha (by rw [GlobalTheory.MixModel.HypDec.extX_apply]; exact mxAt_mul_right haf _)

end GlobalTheory.AscFin.PieceA

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.PieceA

theorem finLat_pcBF_A₁ : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  have H := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at H ⊢
  delta All at H ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  exact finLat_comap_extX _ ((H D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).1

end GlobalTheory.AscFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.givenStageFunction_rowArrow_eq_halfExtension : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e₀ G.pl.W0 → (∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m), GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  first | exact @GlobalTheory.CosetRow.givenFn_right_eq_extFn | exact GlobalTheory.CosetRow.givenFn_right_eq_extFn | (intros; apply GlobalTheory.CosetRow.givenFn_right_eq_extFn <;> assumption)
end

