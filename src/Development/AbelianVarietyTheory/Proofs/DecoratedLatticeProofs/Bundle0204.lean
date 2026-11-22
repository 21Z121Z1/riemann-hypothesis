import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem zEll_mem_ratMx (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨Matrix.vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  funext i j
  change incA D (z i * (if j.1 + 1 = ρ then (1 : D.host.E) else 0)) = ratV z i * ell D ρ j
  simp only [ratV, ell]
  split_ifs <;> simp

theorem incAdj_yZero_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) :
    d.incAdj S (yZero S ρ z) ∈ ratMx D T.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    rw [yZero]; exact neg_mem (zEll_mem_ratMx S ρ z)
  rw [HypDec.incAdj_apply, HypDec.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    star (ψ x) = ψ (-x) := by
  change (starRingEnd ℂ) (ψ x) = _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem integrand_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (f : WO V₀ W → ℂ)
    (hf : IsThetaFunO ψ V₀ W f) (b : Mx D ρ V₀.rank) :
    star (psiBes ψ dV 1 z (dV.nB b)) * f (xZero dW ⬝ b) =
      heisO ψ V₀ W (dW.incX V₀ b) (heisO ψ V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (heisO ψ V₀ W (dW.inc0 V₀ 0) f)) 0 := by
  rw [HypDec.integrandT_eq, ← psi_yZero ψ dV dW z b, star_psi hψ, map_zero, add_zero]
  obtain ⟨γ, hγ⟩ := incAdj_yZero_mem dW V₀ z
  have hx : dW.incX V₀ b = xZero dW ⬝ b := rfl
  have hq := hf.quasi γ (xZero dW ⬝ b)
  rw [show ratW W V₀ γ = dW.incAdj V₀ (yZero V₀ ρ z) from hγ] at hq
  rw [hx, add_comm (xZero dW ⬝ b), hq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hc : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add, add_halves, map_one]
  have hs : symplO V₀ W (xZero dW ⬝ b) (dW.incAdj V₀ (yZero V₀ ρ z)) =
      -symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) := GlobalTheory.OrientedHeis.symplO_skew _ _
  rw [symplOH, symplOH]
  linear_combination (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) * hc -
    algebraMap D.host.F (AF D.host.F) (1 / 2) * hs

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

theorem fl_eq_flatBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ →
      fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  intro D ψ ρ B J s Ψ hΨ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flatBF flat flatAt
  congr 1
  funext u
  simp only [flFun, flatFun, evalAt, HypDec.mixT]
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact integrand_eq hψ B.d J.d _ _ (hf _) b

end GlobalTheory.Unf.StepFour
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SuppFirst

theorem e_mul_ι {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π, p.π_ι]

theorem ι_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h

theorem ι_one' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem shift_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) :
    (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have h1 : p.ι x * (1 - p.e) = 0 := by
    rw [mul_sub, mul_one, mul_comm, e_mul_ι, sub_self]
  have h2 : (1 - p.e) * p.ι y = 0 := by
    rw [sub_mul, one_mul, e_mul_ι, sub_self]
  have h3 : (1 - p.e) * (1 - p.e) = 1 - p.e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  rw [ι_mul', add_mul, mul_add, mul_add, h1, h2, h3, add_zero, zero_add]

def shiftU {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι (x⁻¹ : kˣ) + (1 - p.e), by
      rw [shift_mul, Units.mul_inv, ι_one']; ring, by
      rw [shift_mul, Units.inv_mul, ι_one']; ring⟩
  map_one' := by ext; simp [ι_one']
  map_mul' x y := by ext; simp [shift_mul]

theorem exists_comp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (χ : (AE D)ˣ →* Circle) : ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  refine ⟨Circle.toUnits.comp (χ.comp (shiftU p)), fun x a ha => ?_⟩
  have : shiftU p x = a := Units.ext ha.symm
  simp [this]

theorem card_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k N Y) :
    Fintype.card Y = N := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Fr.γ Fr.β
    rw [Fr.γβ, Matrix.rank_one] at h
    have h' := Matrix.rank_le_card_width Fr.γ
    rw [Fintype.card_fin] at h'
    exact h.trans h'
  · have h := Matrix.rank_mul_le_left Fr.β Fr.γ
    rw [Fr.βγ, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_le_card_width Fr.β)

def prH {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (a : D.host.E) : prH p a = p.pr a := rfl

theorem exists_coreFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : ∃ C : Frame k B.V₀.rank (n₀ ⊕ Unit), p.IsCoreFrame B F.s F.F₀ C := by
  obtain ⟨hc, hA, -, hz, -⟩ := F.bes
  let M : Matrix (Fin B.V₀.rank) (n₀ ⊕ Unit) k :=
    fromCols (B.o.iA.map p.pr * F.F₀.β) (Matrix.of fun r (_ : Unit) => F.s * p.pr (vecB B.o B.ζ r))
  let f : n₀ ⊕ Unit → n₀ ⊕ Fin (c + 1 + 1 + 1) := Sum.elim Sum.inl fun _ => Sum.inr ⟨σ + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (a | _) (b | _) h <;> simp_all [f]
  have key : B.d.i₀.map p.pr * M = F.G₀.β.submatrix id f := by
    ext r (a | _)
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inl, submatrix_apply, id, Sum.elim_inl]
      rw [hA r a, ← Matrix.mul_assoc]
      have hm : B.d.i₀.map p.pr * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr :=
        (Matrix.map_mul (f := prH p)).symm
      rw [hm]
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inr, submatrix_apply, id, Sum.elim_inr]
      rw [hz ⟨σ + 1, by omega⟩ rfl r]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, mulVec, dotProduct]
      rw [← prH_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, prH_apply, prH_apply]
      ring
  let L : Matrix (n₀ ⊕ Unit) (Fin B.V₀.rank) k := F.G₀.γ.submatrix f id * B.d.i₀.map p.pr
  have hLM : L * M = 1 := by
    simp only [L, Matrix.mul_assoc, key]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, F.G₀.γβ]
    exact Matrix.submatrix_one _ hf
  have hcard : Fintype.card (n₀ ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame F.G₀
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hML : M * L = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (n₀ ⊕ Unit) (Fin B.V₀.rank) k (A := L) (B := M) (by simpa using hcard)).mp hLM
  refine ⟨⟨M, L, hML, hLM⟩, fun r a => ?_, fun r => ?_⟩
  · simp [M]
  · simp [M]

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k V.rank Y) : p.IsLoc Fr 1 1 := by
  obtain ⟨hloc, -, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  obtain ⟨g₀, hg₀, hu⟩ := (hloc V Y Fr).1 1
  have h2 := (hloc V Y Fr).2.2 _ _ _ _ hg₀ hg₀
  rw [mul_one] at h2
  have e : g₀ * g₀ = g₀ := hu _ h2
  have : g₀ = 1 := by
    have := congrArg (g₀⁻¹ * ·) e
    simpa [← mul_assoc] using this
  exact this ▸ hg₀

theorem gsupp1 : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  intro D hOm hFl hSym k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ hμ T₁ hT₁ Φ₁ hΦ₁ h hh hne
  obtain ⟨hloc, hjac, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_isUnitVol k
  haveI := hν.1
  obtain ⟨hk, hhk⟩ := (hloc J.W _ F.G₁).2.1 h hh
  have hc : c = 2 * σ := by have := F.bes.1; omega

  obtain ⟨μT, hT⟩ := exists_comp p s₁.χW
  have hS : p.IsComp s₁.χV (S.μ (j + 1))⁻¹ := by
    intro x a ha
    have := hμ x a ha
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at this ⊢
    rw [this, inv_inv]

  let Φ' : SB (Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1)) 1 hk Φ₁.1, om_mem_SB (μ := S.μ (j + 1)) (1 : GL _ k) hk Φ₁.2⟩
  have hom : s₁.om (1, h) (T₁ Φ₁) = T₁ Φ' := by
    refine hOm k p ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil _ μT hS hT _ _ F.G₀ F.G₁ T₁ hT₁ 1 1 h hk
      (isLoc_one p _) hhk Φ₁ Φ' ?_
    simp [Φ']

  obtain ⟨C, hC⟩ := exists_coreFrame p F
  obtain ⟨T₀, -, hT₀⟩ := hFl k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C F.G₀ F.F₁ F.G₁
    hC F.bes F.jac T₁ hT₁
  have hSB := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1
    (by omega)).1 Φ'.1 Φ'.2
  have hflat := hT₀ Φ' ⟨_, hSB⟩ rfl
  rw [hom, hflat] at hne
  have hne' : GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) (om (S.μ (j + 1)) 1 hk ((S.T t).Phi j (c + 1 + 1) (by omega))) ≠ 0 := by
    intro h0
    apply hne
    have : (⟨_, hSB⟩ : SB _) = 0 := by
      ext1
      simpa [Φ', hΦ₁] using h0
    rw [this, map_zero]
  obtain ⟨β, q, hq, u, hu, hkeq⟩ := (hSym k ν hν s κ S t).1 j (c + 1) (by omega) (σ + 1) (by omega) hk hne'
  obtain ⟨r, hr, -⟩ := (hloc J.W _ F.G₁).1 (colE (c + 1 + 1) (σ + 1 + 1) β * q)
  obtain ⟨u', hu', -⟩ := (hloc J.W _ F.G₁).1 u
  have hprod := (hloc J.W _ F.G₁).2.2 _ _ _ _ hr hu'
  rw [← hkeq] at hprod
  obtain ⟨g', -, huniq⟩ := (hloc J.W _ F.G₁).1 hk
  refine ⟨r, hjac _ _ _ _ _ _ _ _ F.jac r β q hq hr, hr.1, u', u, hu', hu, ?_⟩
  exact (huniq _ hhk).trans (huniq _ hprod).symm

end GlobalTheory.LocMod.SuppFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_level_compact_translates_thetaFunction D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenValAddSegL
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHecke.StringEig

open GlobalTheory.ChainOnto (esymm_add_C esymm_map_mul_C esymm_string esymm_eq_zero_of_lt sqrt_sq_C natCast_cpow_half)

theorem map_coe_segL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) (t : ℕ) :
    (segL ϖ z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [segL, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  congr 1
  rw [GlobalTheory.MellinPoly.absPow_eq_zpow, ord_eq_one hϖ, zpow_one, ← natCast_cpow_half]
  congr 1
  push_cast
  ring

theorem genVal_add_segL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r N t n₀ : ℕ) (B : Multiset ℂˣ) (zS zT : ℂˣ), B.card = N → n₀ ≤ N + t → genVal (resCard k) r (N + t) (B.map (· * (zS * zT⁻¹)) + segL ϖ zS t) n₀ = (zS : ℂ) ^ n₀ * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n₀ * (r + N)) * ∑ n ∈ Finset.range (N + 1), (if n ≤ n₀ then ((resCard k ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin (resCard k) t (n₀ - n) : ℕ) : ℂ) else 0) * (((zT : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (r + N + t)))⁻¹ * genVal (resCard k) r N B n) := by
  intro k _ _ _ _ ϖ hϖ r N t n₀ B zS zT hB hn₀
  set Q := resCard k with hQdef
  have hsQ := sqrt_sq_C Q
  have hs : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < Q := one_lt_resCard k
    have : ((Q : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : Q ≠ 0) (by exact_mod_cast this)
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  have hA : (B.map (· * (zS * zT⁻¹))).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((zS : ℂ) * (zT : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def, mul_comm]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = N := by simp [hB]
  set F : ℕ → ℂ := fun n => (if n ≤ n₀ then ((Q ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin Q t (n₀ - n) : ℕ) : ℂ) else 0) *
    (((zT : ℂ) ^ n * s ^ (n * (r + N + t)))⁻¹ * genVal Q r N B n) with hF
  have hFa : ∀ j, N < j → F j = 0 := by
    intro j hj
    simp only [hF, genVal, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, n₀ < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ n₀ by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (N + 1), F j = ∑ j ∈ Finset.range (n₀ + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show N + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show n₀ + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, genVal, Multiset.map_add, esymm_add_C, Finset.mul_sum, Finset.mul_sum, hA, map_coe_segL k ϖ hϖ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ n₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s zS hs hsQ t]
  simp only [hF, if_pos hjk, genVal]
  by_cases hjN : j ≤ N
  · by_cases hat : n₀ - j ≤ t
    · have hsI : s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ)))) =
          s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j)) := by
        rw [← pow_mul]
        simp only [← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hs]
        congr 1
        push_cast [Nat.cast_sub hjN, Nat.cast_sub hjk, Nat.cast_sub hat, Nat.cast_sub hn₀]
        ring
      have hz : ((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j) = (zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹ := by
        rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk, inv_pow]
      calc _ = (s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ))))) *
            (((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j)) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
        _ = (s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j))) *
            ((zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
        _ = _ := by rw [hsQ]; push_cast; rw [mul_inv]; ring
    · rw [Formalism.L2.Col.gaussBin_eq_zero Q (show t < n₀ - j by omega)]
      simp
  · rw [esymm_eq_zero_of_lt _ (by omega)]
    simp

end GlobalTheory.ParHecke.StringEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugate
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem typePlaces_noConj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg →
    ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg hT PP hP PP' hP' hc
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hFfix : ∀ r : 𝓞 D.host.F,
      D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) :=
    fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

  have hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F) := by
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap] at hr ⊢
    obtain ⟨c', hc', he⟩ := hc _ hr
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
      apply RingOfIntegers.ext
      rw [he, hstar, hFfix]
    rwa [← this]
  have hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal
  have hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤ := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top
  have hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    exact (hmax.eq_of_le hne hle).symm
  have hgP := hT.1 PP hP
  have hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hgP
  obtain ⟨W, _, hW⟩ := hT.2 _ hgv
  have e1 : PP = W := hW PP ⟨hP, rfl⟩
  have e2 : PP' = W := hW PP' ⟨hP', hund⟩
  have e : PP' = PP := e2.trans e1.symm
  subst e

  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    rw [Nat.cast_mul] at hgP
    rcases PP'.isPrime.mem_or_mem hgP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨x, hx, hxn⟩ :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1
  obtain ⟨c', hc', he⟩ := hc x hx
  exact hxn c' (he.trans (hstar _)) hc'

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasTypes R lam := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | exact GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | (intros; apply GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegmentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_value_inert_place_and_segment : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  first | exact @GlobalTheory.ChainOnto.val_seg_of_isInertAt | exact GlobalTheory.ChainOnto.val_seg_of_isInertAt | (intros; apply GlobalTheory.ChainOnto.val_seg_of_isInertAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  first | exact @GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | exact GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val <;> assumption)
end

