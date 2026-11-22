import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasuresStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFinite_covolume_one_matrix_unitriangular_measures : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  first | exact @GlobalTheory.Unf.sFinite_vol | exact GlobalTheory.Unf.sFinite_vol | (intros; apply GlobalTheory.Unf.sFinite_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
section
noncomputable section

namespace GlobalTheory.ChainOnto.SatHeckeChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem heckeVec_eq_smul_of_isSatVecGL :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ),
      ∀ φ ∈ Hecke ℂ (KGL w n), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V),
          IsSatVecGL w ρ x B → heckeVec ρ (KGL w n) φ x = z • x := by
  intro E _ _ w n B φ hφ
  by_cases hB : B.card = n
  · obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
      obtain ⟨l, rfl⟩ := Quot.exists_rep B
      obtain rfl : l.length = n := hB
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
    obtain ⟨x₀, hx₀⟩ := (hasSatGL_psFunGL (w := w) α).exists_vec
    obtain ⟨z, hz, -⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx₀ φ hφ
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    obtain ⟨c, e1, e2⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx φ hφ
    have e : z = c := smul_left_injective ℂ hx₀.1 (hz.symm.trans e1)
    rw [e2, e]
  · exact ⟨0, fun V _ _ ρ x hx => absurd hx.2.2.1 hB⟩

end GlobalTheory.ChainOnto.SatHeckeChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBounStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_uniformly_locallyConstant_bounded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.SBUnif.uniform | exact GlobalTheory.SBUnif.uniform | (intros; apply GlobalTheory.SBUnif.uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
section
noncomputable section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

namespace GlobalTheory.FinPl.SBFacts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem charInd_mem (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hK : IsCompact (Q.lat : Set (n → k)) := GlobalTheory.FinPl.Comm.isCompact_lat Q.lat
  refine ⟨?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun y => ?_
    by_cases hy : y ∈ Q.lat
    · refine ⟨(fun z => z - y) ⁻¹' (Q.ker : Set (n → k)), (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat Q.ker).preimage (by fun_prop),
        by simp [Q.ker.zero_mem], fun z hz => ?_⟩
      have hw : Q.HasVal (z - y) 0 := Pair.mem_ker.1 hz
      have hz' : Q.HasVal z (Q.ev y) := by
        simpa using hw.add (Pair.hasVal_ev hy)
      have hzl : z ∈ Q.lat := hz'.mem
      simp only [charInd, vecInd, if_pos hzl, if_pos hy, hz'.ev_eq]
    · refine ⟨(Q.lat : Set (n → k))ᶜ, hK.isClosed.isOpen_compl, hy, fun z hz => ?_⟩
      have hz' : z ∉ Q.lat := hz
      simp only [charInd, vecInd, if_neg hz', if_neg hy, mul_zero]
  · have hy' : y ∉ Q.lat := hy
    simp only [charInd, vecInd, if_neg hy', mul_zero]

end GlobalTheory.FinPl.SBFacts

theorem GlobalTheory.FinPl.sb_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) →
      GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧
    ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, fun Λ hΛ => ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  haveI := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDStable

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (a : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (a • y) x = a * hermAt S y x := by
  unfold hermAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem smul_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  intro D S v Λ hΛ a ha y hy
  have hsupp : ∀ i, (a • y) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hΛ.1 y hy i)
  refine (hΛ.2.2 (a • y) hsupp).2 fun x hx => ?_
  rw [hermAt_smul_left]
  exact mul_mem_intAt ha ((hΛ.2.2 y (hΛ.1 y hy)).1 hy x hx)

end GlobalTheory.IwaPlace.SDStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∃ α β : Fin ρ → AE D, (∀ i, α i ∈ idAt D (· = v)) ∧ (∀ i, β i ∈ idAt D (· = v)) ∧ (∀ i, α i * β i = ε) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a * β i ∈ intAt D (· = v)) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jY i a ∈ latV S L (· = v) ↔ a * cA D (α i) ∈ intAt D (· = v)) := by
  first | exact @GlobalTheory.IwaIdeals.ideals_at_place | exact GlobalTheory.IwaIdeals.ideals_at_place | (intros; apply GlobalTheory.IwaIdeals.ideals_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S), IsSelfDualC S L →
    ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ := by
  first | exact @GlobalTheory.FinPl.FrameLat.exists_lat | exact GlobalTheory.FinPl.FrameLat.exists_lat | (intros; apply GlobalTheory.FinPl.FrameLat.exists_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_haar_measure_fundamental_domain : ∀ (D : D7) (S H : HSp D) (N : Subgroup (GA D S)) (s : GA D H →* GA D S), Continuous s → IsClosed (N : Set (GA D S)) → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') → (∀ n ∈ N, ∀ h, n * s h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ H) → ∀ (vH : Vol H) (ν : Measure N) (𝓝 : Set N), ν.IsHaarMeasure → IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν → (semiMeas N s vH.μ ν).IsHaarMeasure → ∃ 𝓡 : Set (N ⊔ s.range : Subgroup (GA D S)), IsFundamentalDomain ((GQ S ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) 𝓡 (semiMeas N s vH.μ ν) ∧ ∀ f : GA D S → ℂ, Measurable f → (IntegrableOn (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) 𝓡 (semiMeas N s vH.μ ν) ↔ AbsConv vH.μ vH.𝓕 ν 𝓝 fun h n => f (n.1 * s h)) ∧ (AbsConv vH.μ vH.𝓕 ν 𝓝 (fun h n => f (n.1 * s h)) → ∫ r in 𝓡, f (r : GA D S) ∂(semiMeas N s vH.μ ν) = ∫ h in vH.𝓕, ∫ n in 𝓝, f (n.1 * s h) ∂ν ∂vH.μ) := by
  first | exact @GlobalTheory.Unf.semiFd_iterated | exact GlobalTheory.Unf.semiFd_iterated | (intros; apply GlobalTheory.Unf.semiFd_iterated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SnocColumnsMovedByUpperUnitriangularIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.BlockUni

theorem unitri_isUnit {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (h0 : ∀ i j, j < i → A i j = 0) (h1 : ∀ i, A i i = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hb : A.BlockTriangular id := fun i j h => h0 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [h1]

theorem snoc_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  intro R _ n σ M w Y
  set x : Matrix (Fin n) (Fin (σ+1)) R := Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) with hx
  have hxc : ∀ k i, x k (Fin.castSucc i) = M k i := by intro k i; simp [hx]
  have hxl : ∀ k, x k (Fin.last σ) = w k := by intro k; simp [hx]
  have col : ∀ (U : Matrix (Fin (σ+1)) (Fin (σ+1)) R) k j,
      (x * U) k j = ∑ i, M k i * U (Fin.castSucc i) j + w k * U (Fin.last σ) j := by
    intro U k j; rw [Matrix.mul_apply, Fin.sum_univ_castSucc]; simp only [hxc, hxl]
  have Ycol : ∀ k j, (Y * x) k (Fin.castSucc j) = (Y * M) k j := by
    intro k j; simp only [Matrix.mul_apply, hxc]
  have Ylast : ∀ k, (Y * x) k (Fin.last σ) = (Y *ᵥ w) k := by
    intro k; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hxl]
  constructor
  · rintro ⟨U, hU, hE⟩
    have hU' := (GlobalTheory.UniIndexPrime.mem_uniSub U).1 hU
    let u : Matrix (Fin σ) (Fin σ) R := Matrix.of fun i j => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.castSucc j)
    have hu0 : ∀ i j, j < i → u i j = 0 := fun i j h =>
      hU'.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 h)
    have hu1 : ∀ i, u i i = 1 := fun i => hU'.2 _
    refine ⟨(unitri_isUnit u hu0 hu1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hu0, hu1⟩,
      fun i => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.last σ), ?_, ?_⟩
    · ext k j
      have h := congrFun (congrFun hE k) (Fin.castSucc j)
      rw [Ycol, col] at h
      rw [h, IsUnit.unit_spec, Matrix.mul_apply]
      have h0 : (U : Matrix _ _ R) (Fin.last σ) (Fin.castSucc j) = 0 := hU'.1 _ _ (Fin.castSucc_lt_last j)
      simp [h0, u]
    · ext k
      have h := congrFun (congrFun hE k) (Fin.last σ)
      rw [Ylast, col, hU'.2 (Fin.last σ)] at h
      rw [h]; simp only [Pi.add_apply, Matrix.mulVec, dotProduct]; ring
  · rintro ⟨u, hu, v, h1, h2⟩
    have hu' := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
    let U : Matrix (Fin (σ+1)) (Fin (σ+1)) R := Matrix.of fun a b =>
      Fin.lastCases (Fin.lastCases (1 : R) (fun _ => 0) b)
        (fun i => Fin.lastCases (v i) (fun j => (u : Matrix _ _ R) i j) b) a
    have Ucc : ∀ i j, U (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
      intro i j; simp [U]
    have Ucl : ∀ i, U (Fin.castSucc i) (Fin.last σ) = v i := by intro i; simp [U]
    have Ulc : ∀ j, U (Fin.last σ) (Fin.castSucc j) = 0 := by intro j; simp [U]
    have Ull : U (Fin.last σ) (Fin.last σ) = 1 := by simp [U]
    have hU0 : ∀ a b, b < a → U a b = 0 := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (lt_irrefl _)
        | cast j => exact Ulc j
      | cast i =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => rw [Ucc]; exact hu'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hab)
    have hU1 : ∀ a, U a a = 1 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact Ull
      | cast i => rw [Ucc]; exact hu'.2 i
    refine ⟨(unitri_isUnit U hU0 hU1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hU0, hU1⟩, ?_⟩
    rw [IsUnit.unit_spec]
    ext k b
    induction b using Fin.lastCases with
    | last =>
      rw [Ylast, col, h2, Ull]
      simp only [Ucl, Pi.add_apply, Matrix.mulVec, dotProduct]; ring
    | cast j =>
      rw [Ycol, col, h1, Matrix.mul_apply]
      simp only [Ucc, Ulc]; ring

end GlobalTheory.BlockUni
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl

theorem SplitPt.sec_mem_idAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.sec a = p.e * p.sec a := by
    have := p.sec_pr (p.sec a)
    rwa [p.pr_sec] at this
  rw [(placeIdem_acts D p.v ε hε).1, ← hsum, he, ← mul_assoc, add_mul, p.split.1,
    mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]

theorem mt_mul_mt_inv {D : D7} (S : HSp D) (γ : GA D S) : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Frame.isLat_of_isLatMoved : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  intro D k _ _ _ _ p S n _ _ β γ L M Λ hM hL x
  have hsupp : ∀ i, (Formalism.L2.Theta.mt S γ⁻¹ *ᵥ fun i => p.sec ((β.b *ᵥ x) i)) i ∈ idAt D (· = p.v) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (p.sec_mem_idAt _)
  rw [hL x, hM _ hsupp, Matrix.mulVec_mulVec, mt_mul_mt_inv, Matrix.one_mulVec]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_self (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h := p.sec_pr (p.sec a * p.sec b)
  rw [map_mul, p.pr_sec, p.pr_sec] at h
  rw [h, ← mul_assoc, sec_self]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  have h := p.sec_pr 1
  rwa [map_one, mul_one] at h

theorem splitPlaceSection_add_complement_mul (p : SplitPt D k) (a b : k) :
    (p.sec a + (1 - p.e)) * (p.sec b + (1 - p.e)) = p.sec (a * b) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p a
  have hb := sec_self p b
  rw [sec_mul]
  linear_combination (-1 : AE D) * ha + (-1 : AE D) * hb + he

def idl (p : SplitPt D k) : kˣ →* (AE D)ˣ where
  toFun a := ⟨p.sec a + (1 - p.e), p.sec ((a⁻¹ : kˣ) : k) + (1 - p.e),
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, sec_one]; ring,
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, sec_one]; ring⟩
  map_one' := Units.ext (by simp only [Units.val_one, sec_one]; ring)
  map_mul' a b := Units.ext (by simp only [Units.val_mul, splitPlaceSection_add_complement_mul])

theorem idl_val (p : SplitPt D k) (a : kˣ) : ((idl p a : (AE D)ˣ) : AE D) = p.sec (a : k) + (1 - p.e) := rfl

def lam (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) : kˣ →* ℂˣ where
  toFun a := Units.mk0 ((χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _)
      (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _) r).ne'))
  map_one' := Units.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV])
  map_mul' a b := Units.ext (by
    simp only [map_mul, Units.val_mk0, Units.val_mul, Circle.coe_mul, GlobalTheory.SplitLinear.absFin_mul,
      Real.mul_rpow (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le, Complex.ofReal_mul]
    ring)

theorem lam_val (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) (a : kˣ) :
    ((lam p χ r a : ℂˣ) : ℂ) = (χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ) := rfl

end GlobalTheory.SplitLinAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) → Continuous χ ∧ χ ≠ 1 := by
  first | exact @GlobalTheory.FinPl.SplitChar.cont_ne_one | exact GlobalTheory.FinPl.SplitChar.cont_ne_one | (intros; apply GlobalTheory.FinPl.SplitChar.cont_ne_one <;> assumption)
end

