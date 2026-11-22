import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0778
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0779
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0504
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0343

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem eventually_cv_mem_intLoc {D : D7} (a : AE D) :
    ∀ᶠ v : Pl D in cofinite, cv D v a ∈ intLoc D.host.F D.host.E v :=
  GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a

theorem isOpen_intAll (D : D7) : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
  GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere

theorem exists_intOff {D : D7} {a b : ℕ} (x : Mx D a b) :
    ∀ᶠ v : Pl D in cofinite, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)

theorem isOpen_nearInt {D : D7} {a b : ℕ} (x : Mx D a b) :
    IsOpen {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} =
      ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  have hT := (top_mx (D := D) a b).1
  haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  have hc : Continuous fun y : Mx D a b => y - x := continuous_id.sub continuous_const
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_intAll D).preimage (hc.matrix_elem i j)

theorem nuT_intOff_ne_zero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
      nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  intro D n t B W d hn I μ hμ x₀
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t :=
    fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
  let p₀ : I.l.K × Par D n t W := (1, (1, (0, 0)))
  have hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite :=
    ((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))
  refine ⟨hbad.toFinset, fun S hS => ?_⟩
  have hπ : Continuous π := by
    obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
    exact (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  let N : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    {z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}
  have hNo : IsOpen N := ((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter
    ((isOpen_nearInt (π p₀).2).preimage continuous_snd)
  have hN0 : π p₀ ∈ N := by
    constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]
  have hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2} := by
    intro z hz
    have key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
        ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v := fun v hv => by
      by_contra hc
      exact hv (hS (hbad.mem_toFinset.2 hc))
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · have := add_mem (hz.1 i j v) ((key v hv).1 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
    · have := add_mem (hz.2 i j v) ((key v hv).2 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hGB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.haarK
  have hs1 : SigmaFinite (I.μ₁.prod μ) := inferInstance
  have hs2 : SigmaFinite (Q0 I μ) := sigmaFinite_parameter_product_measure I μ hμ
  have p1 : (I.μ₁.prod μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have p2 : (Q0 I μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hopen : IsOpen (π ⁻¹' N) := hNo.preimage hπ
  have hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0 := hopen.measure_ne_zero _ ⟨p₀, hN0⟩
  intro h0
  apply hne
  have hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} :=
    Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _
  exact le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansion
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.PcShear

theorem jc_zero {D : D7} {ρ p : ℕ} (y : Mx D ρ p) : GlobalTheory.CompanionTheory.FJE.jc y 0 = 0 := by
  apply Subtype.ext
  have h : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  show (HMul.hMul y (adj (0 : Mx D ρ p)) : Mx D ρ ρ) + (HMul.hMul (0 : Mx D ρ p) (adj y) : Mx D ρ ρ) = _
  rw [h]
  simp

theorem chz_neg {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (z : hermA D ρ) : chz ψ b₀ (-z) = conj (chz ψ b₀ z) := by
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have hne : chz ψ b₀ (0 : hermA D ρ) ≠ 0 := by
      intro h'
      have := hnorm 0
      rw [h'] at this
      simp at this
    exact (mul_eq_left₀ hne).1 h.symm
  have h1 : chz ψ b₀ z * chz ψ b₀ (-z) = 1 := by
    rw [← hadd, add_neg_cancel, h0]
  have h2 : chz ψ b₀ z * conj (chz ψ b₀ z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hne : chz ψ b₀ z ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem zc_sh {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) (hF : LeftInv (GF D n) F)
    (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (k : G D n) :
    zc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * k) = zc M m ψ b₀ F k := by
  unfold zc
  congr 1
  funext z
  have hc : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx z 0 = M.nzx z 0 * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) z 0
    rwa [jc_zero, add_zero] at this
  have hr : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n := (GlobalTheory.T.rational_points_heisenberg_group M).1 ξ
  rw [← mul_assoc, ← hc, mul_assoc, hF _ hr]

theorem zc_at {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (F : G D n → ℂ)
    (hF : LeftInv (GF D n) F) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n) (x : Mx D ρ p) :
    zc M m ψ b₀ F (M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h)) =
      conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) := by
  set c : hermA D ρ := -GlobalTheory.CompanionTheory.FJE.jc (GlobalTheory.CompanionTheory.FJE.rt ξ) x with hc
  have h1 : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx c x = M.nzx 0 x * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) c x
    rwa [hc, neg_add_cancel] at this
  have h2 : M.nzx c x = M.nzx c 0 * M.nzx 0 x := by
    rw [GlobalTheory.CompanionTheory.NzxAdd.nzx_add, add_zero, zero_add]
  have h3 : M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * (M.nzx c 0 * (M.nzx 0 x * h)) := by
    rw [← mul_assoc, ← h1, h2]
    simp only [mul_assoc]
  rw [h3, zc_sh M m ψ b₀ F hF, GlobalTheory.T.centre_coefficient_equivariance M m ψ hψ b₀ F hF, hc, chz_neg ψ hψ, GlobalTheory.T.centre_character_commutator]

theorem pc_sh : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  intro D n ρ p hn M m ψ hψ b₀ F hF ξ h
  unfold PositivityTheory.Rg.Rsw.pc
  congr 1
  funext x
  exact zc_at M m ψ hψ b₀ F hF ξ h x

end GlobalTheory.CompanionTheory.FJE.PcShear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ThTot
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.ThTot.OneRow

variable {D : D7}

theorem evalPoly_temperate {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  have coord : ∀ k : D.what₂.Tau × Fin m × Fin n × Bool, Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
    rintro ⟨τ, i, j, b⟩
    let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))
    cases b
    · exact L.hasTemperateGrowth
    · exact (Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evalPoly] using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + fun z => evalPoly q (fun τ => Matrix.of (z τ)) := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * fun z =>
          if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.mul (coord k)

theorem exists_schwartz_poly_gauss (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z,
      f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine ⟨SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ (fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    evalPoly p (fun τ => Matrix.of (z τ))) f, fun z => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evalPoly_temperate p)]
  simp [hf]

theorem fockA_le_schwartzA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := exists_schwartz_poly_gauss n V l hl s hs p
  refine Submodule.subset_span ⟨f, g, hg, ?_⟩
  funext x
  rw [hf]
  rfl

theorem gram_rank_one_one : (V1 D).gram = 1 := by
  refine Matrix.ext fun (i j : Fin 1) => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  show ∑ k : Fin 1, star ((Pi.basisFun D.host.E (Fin 1)) 0 k) * Formalism.BasicNotions.Examples₂.sgn false * (Pi.basisFun D.host.E (Fin 1)) 0 k =
    (1 : Matrix (Fin 1) (Fin 1) D.host.E) 0 0
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  unfold gramAt
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cartan_involution_rank_one (τ : D.what₂.Tau) : IsCartanInv (gramAt D (V1 D) τ) 1 := by
  rw [gram_at_place_rank_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem gram_rank_one_eq_one : gA (V1 D) = (1 : Mx D (V1 D).rank (V1 D).rank) := by
  unfold gA rat
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

set_option synthInstance.maxHeartbeats 400000 in
theorem incA_algebraMap (c : D.host.F) :
    incA D (algebraMap D.host.F D.host.E c) = (algebraMap D.host.F (AF D.host.F) c) • (1 : AE D) := by
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c) =
    (algebraMap D.host.F (AF D.host.F) c) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem pr_eq {p : ℕ} (b₀ : HermE D 1) (c : D.host.F) (hc : algebraMap D.host.F D.host.E c = b₀.1 0 0)
    (x y : Mx D 1 p) :
    pr b₀ x y = (algebraMap D.host.F (AF D.host.F) c) • (inner (V1 D) x y : Mx D p p) := by
  have h1 : b₀.1.map (incA D) = (algebraMap D.host.F (AF D.host.F) c) • (1 : Mx D 1 1) := by
    refine Matrix.ext fun (i j : Fin 1) => ?_
    fin_cases i; fin_cases j
    simp [← hc, incA_algebraMap]
  have h2 : (inner (V1 D) x y : Mx D p p) = HMul.hMul (adj x) y := by
    unfold GlobalTheory.StdUnn.inner
    rw [gram_rank_one_eq_one]
    exact congrArg (fun t : Mx D 1 p => (HMul.hMul (adj x) t : Mx D p p)) (Matrix.one_mul y)
  rw [h2]
  unfold pr
  rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem trA_smul (a : AF D.host.F) (z : AE D) : trA (a • z) = a * trA z := by
  simp [trA, map_smul]

theorem halfTr_smul (a : AF D.host.F) (z : AE D) : halfTr (a • z) = a * halfTr z := by
  simp only [halfTr, trA_smul]; ring

theorem exists_base (b₀ : HermE D 1) (h : b₀.1.det ≠ 0) :
    ∃ c : D.host.F, c ≠ 0 ∧ algebraMap D.host.F D.host.E c = b₀.1 0 0 := by
  have h0 : b₀.1 0 0 ≠ 0 := by simpa [Matrix.det_fin_one] using h
  have hfix : star (b₀.1 0 0) = b₀.1 0 0 := congrFun (congrFun b₀.2 0) 0
  have hF : b₀.1 0 0 ∈ D.host.F :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).1 hfix
  exact ⟨⟨_, hF⟩, fun e => h0 (by simpa using congrArg (fun u : D.host.F => (u : D.host.E)) e), rfl⟩

theorem exists_par (ψ₀ : AddChar (AF D.host.F) ℂ) (h₀ : IsStdChar D ψ₀ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (a : D.host.F) (ha : a ≠ 0) :
    IsCharAF D.host.F (shift ψ₀ a) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ₀ a) θ l ∧ ∀ τ, l τ ≠ 0 := by
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have haE : algebraMap D.host.F D.host.E a ≠ 0 := (map_ne_zero _).2 ha
  have hst : star (algebraMap D.host.F D.host.E a) = algebraMap D.host.F D.host.E a :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hsk : IsSkew (-D.host.xi0 / algebraMap D.host.F D.host.E a) := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) haE, ?_⟩
    rw [star_div₀, star_neg, hst, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, neg_div]
  obtain ⟨lam, hlam, hc, l, hp, habs⟩ := shift_char_realPar D ψ₀ h₀ θ hθ _ hsk
  have : lam = a := by
    apply (algebraMap D.host.F D.host.E).injective
    rw [hlam]
    field_simp
  subst this
  refine ⟨hc, l, hp, fun τ h => ?_⟩
  have := habs τ
  rw [h, abs_zero] at this
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 hxi
  have h2 : tauE D τ (-D.host.xi0 / algebraMap D.host.F D.host.E lam) ≠ 0 := (map_ne_zero _).2 hsk.1
  exact (div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)) this.symm

theorem oneTotal : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  intro hC hM hF D p μ 𝓕 hμ ψ hψ b₀ hdet χ hχ hr θ hθ
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, l, hpar, hl⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  intro u huc hub hu
  refine hF D p θ hθ l hl μ 𝓕 hμ u huc hub fun φ hφ => ?_
  have hφS := fockA_le_schwartzA θ (V1 D) p l hl _ (fun τ => cartan_involution_rank_one τ) hφ
  let Φ : schwartzA θ (V1 D).rank p := ⟨φ, hφS⟩
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  have hT : IsTh ψ χ θ b₀ μ (fun h => (ω h Φ).1) :=
    { mem := fun h => (ω h Φ).2
      cont := hC D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
      maj := hM D p _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hpar hl Φ hφ
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }
  have h1 : ∫ y, u y * conj ((ω 1 Φ).1 y) ∂μ = 0 := hu _ hT
  have h2 : (ω 1 Φ).1 = φ := by rw [map_one]; rfl
  rw [h2] at h1
  exact h1

end GlobalTheory.CompanionTheory.ThTot.OneRow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedSizeRatGLMul
section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

noncomputable section
namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem logSize_nonneg_cm {n : ℕ} (g : GA E n) : 0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem redSize_ratGL_mul {n : ℕ} (γ : GL (Fin n) E) (g : GA E n) :
    redSize (ratGL E n γ * g) = redSize g := by
  unfold redSize
  rw [← (Equiv.mulRight γ).iInf_comp (g := fun δ : GL (Fin n) E => logSize (ratGL E n δ * g))]
  refine iInf_congr fun δ => ?_
  simp [map_mul, mul_assoc]

theorem bddBelow_sizes {n : ℕ} (g : GA E n) :
    BddBelow (Set.range fun γ : GL (Fin n) E => logSize (ratGL E n γ * g)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact logSize_nonneg_cm _⟩

theorem redSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  le_ciInf fun _ => logSize_nonneg_cm _

theorem redSize_le {n : ℕ} (g : GA E n) : redSize g ≤ logSize g := by
  have h := ciInf_le (bddBelow_sizes g) (1 : GL (Fin n) E)
  simp only [map_one, one_mul] at h
  exact h

theorem redSize_zero (g : GA E 0) : redSize g = 0 := by
  have h : ∀ A : Matrix (Fin 0) (Fin 0) (Ad E), logSizeM A = 0 := fun A => by
    simp [logSizeM]
  have h' : ∀ x : GA E 0, logSize x = 0 := fun x => by simp [logSize, h]
  simp [redSize, h']

theorem wt_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : H E n 0),
    (∀ γ : GL (Fin n) E, wt ((ratGL E n γ * x.1, x.2) : H E n 0) = wt x) ∧ 1 ≤ wt x ∧ wt x ≤ 1 + logSize x.1 := by
  intro E _ _ _ n x
  refine ⟨fun γ => ?_, ?_, ?_⟩
  · simp only [wt, redSize_ratGL_mul]
  · have h1 := redSize_nonneg x.1
    have h2 := redSize_nonneg x.2
    simp only [wt]; linarith
  · have h1 := redSize_le x.1
    have h2 := redSize_zero x.2
    simp only [wt]; linarith

end GlobalTheory.CompanionTheory.PiVec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeTor
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

namespace GlobalTheory.CompanionTheory.PiVec

theorem sizeTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ω : Set (GA E n)), IsCompact ω → ∃ A : ℝ, 0 ≤ A ∧
    ∀ b ∈ ω, ∀ x : Fin n → ℝ, ∀ k ∈ maxCompact (K := E) (n := n),
      logSize (b * An.tor E x * k) ≤ A + 2 * Module.finrank ℚ E * ‖x‖ := by
  intro E _ _ _ n ω hω
  obtain ⟨hcpt, -, -, c, hc⟩ :=
    GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  obtain ⟨r₁, h₁⟩ := hcpt ω hω
  obtain ⟨r₂, h₂⟩ := hcpt _ (GroundTheory.Automorphic.Reduction.isCompact_maxCompact (K := E) (n := n))
  have htor := GlobalTheory.CompanionTheory.TorNorm.torNorm GlobalTheory.CompanionTheory.LogAbs.logAbsBasic E
  refine ⟨|r₁| + |r₂| + 2 * |c|, by positivity, fun b hb x k hk => ?_⟩
  have e₁ := hc (b * An.tor E x) k
  have e₂ := hc b (An.tor E x)
  have e₃ := ((htor.2 n x).2)
  have a₁ := (h₁ b hb).trans (le_abs_self r₁)
  have a₂ := (h₂ k hk).trans (le_abs_self r₂)
  have a₃ := le_abs_self c
  linarith

end GlobalTheory.CompanionTheory.PiVec

end
end

