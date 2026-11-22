import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in
omit [NumberField E] [IsTotallyComplex E] in

def barKHom : Kinf E a →* Kinf E a where
  toFun := barK
  map_one' := Subtype.ext (by ext i j : 1; simp [barK, Matrix.one_apply])
  map_mul' k k' := Subtype.ext (by
    change Matrix.transpose (star (k.1 * k'.1)) = Matrix.transpose (star k.1) * Matrix.transpose (star k'.1)
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, mul_comm])

omit [NumberField E] [IsTotallyComplex E] in
@[simp] theorem barKHom_apply (k : Kinf E a) : barKHom E a k = barK k := rfl

omit [NumberField E] [IsTotallyComplex E] in

theorem barK_barK (k : Kinf E a) : barK (barK k) = k := Subtype.ext (by
  ext i j
  simp [barK, Matrix.star_apply])

omit [NumberField E] [IsTotallyComplex E] in

theorem barKHom_surjective : Function.Surjective (barKHom E a) := fun k => ⟨barK k, barK_barK k⟩

def cptOn (π : CuspSub E a) : Representation ℂ (Kinf E a) π.V where
  toFun k := π.op (.cpt k)
  map_one' := by
    ext φ
    simp [CuspSub.op, act]
  map_mul' k k' := by
    ext φ
    simp [CuspSub.op, act, map_mul]

@[simp] theorem cptOn_apply (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    cptOn π k φ = π.op (.cpt k) φ := rfl

@[simp] theorem cptOn_val (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    (cptOn π k φ).1 = cptRep E a k φ.1 := rfl

end GlobalTheory.IdemAdj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOneStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_transform_integral_unitary_congruent_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  first | exact @GlobalTheory.Hk3.CayleyCong.cayley_cong | exact GlobalTheory.Hk3.CayleyCong.cayley_cong | (intros; apply GlobalTheory.Hk3.CayleyCong.cayley_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_local_data_integral_off_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  first | exact @GlobalTheory.PhiRootVal.phi_intOff | exact GlobalTheory.PhiRootVal.phi_intOff | (intros; apply GlobalTheory.PhiRootVal.phi_intOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem ringHom_mem_qbar {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map f.toRatAlgHom

theorem lamC_eq_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hs]

theorem chi_alg_unit_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsChi D χ → p ≠ 2 → GL3Theta.InertK D p → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
      χ 𝔞 ∈ TaylorLogMetric.Qbar ∧ χ 𝔞 ≠ 0 ∧ ‖TaylorLogMetric.lamC lam (χ 𝔞)‖ = 1 := by
  intro D p _ lam χ hχ hp2 hin 𝔞 ha
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  set P : ℂ := ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z with hPdef
  have hpow : χ 𝔞 ^ k = P⁻¹ := by
    have h := hχ.2 ⟨z, hzu⟩
    simp only at h
    rw [← hspan, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.chi_pow D χ hχ ha k hk] at h
    rw [h, hPdef, Finset.prod_inv_distrib]
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero _).mpr hz0
  have hP : P ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => ringHom_mem_qbar _ z
  have hk0 : k ≠ 0 := by omega
  have halg : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff] at hP ⊢
    have h2 : IsAlgebraic ℚ (χ 𝔞 ^ k) := by rw [hpow]; exact hP.inv
    exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hk0) h2
  have hne : χ 𝔞 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hpow
    exact hP0 (inv_eq_zero.mp hpow.symm)
  refine ⟨halg, hne, ?_⟩
  have hnu := GlobalTheory.T.norm_prod_cmEmbeddings_eq_one_of_inert D p lam hp2 hin z hz
  rw [← hPdef, lamC_eq_of_mem lam hP] at hnu
  have hsub : (⟨χ 𝔞, halg⟩ : TaylorLogMetric.Qbar) ^ k = (⟨P, hP⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    simp [hpow]
  have e1 : ‖lam ⟨χ 𝔞, halg⟩‖ ^ k = 1 := by
    rw [← norm_pow, ← map_pow, hsub, map_inv₀, norm_inv, hnu, inv_one]
  rw [lamC_eq_of_mem lam halg]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0).mp e1

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFielStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  first | exact @GlobalTheory.PtLocalEig.eig_descends | exact GlobalTheory.PtLocalEig.eig_descends | (intros; apply GlobalTheory.PtLocalEig.eig_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveIdealBaseThetaVectorNormalisedEveryPlace
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.LocMM

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

theorem kappaAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact GlobalTheory.T.kappa_norm_at_splitPrimes D cc δ B hcc hδ p ι hs
  · exact GlobalTheory.T.kappa_on_nonsplit_primes D cc δ B hcc hδ p ι hs

theorem locNormMM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), B.LocNormMM a₀ b₀ ha hd lam hlam p ι := by
  intro D cc δ hcc hδ B a₀ b₀ c₀ ha hd lam hlam hcm hB l _ ι
  have hK : B.KappaAt l ι := kappaAt B hcc hδ l ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  unfold Base.LocNormMM LocNorm
  rw [hω] at h2
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 l Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  refine ⟨B.gC.trans u, B.kappa * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu).le, ?_⟩
  rw [h2, hc, smul_smul]

end GlobalTheory.ThLoc.LocMM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
section
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ConjDualPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

variable (L a) in

def phiA : GA L a := finGL L a (PhiU a (Af L)) * infGL L a (PhiU a (Cinf L))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem invT_map_invT (c : Af L →+* Af L) (k : GL (Fin a) (Af L)) :
    invT a (Af L) (GeneralLinearGroup.map c (invT a (Af L) k)) = GeneralLinearGroup.map c k := by
  ext i j
  rfl

theorem rt_phiA_act (o : Op L a) :
    rt L a (phiA L a) * act (conjOp o) = act (thetaOp (invTOp o)) * rt L a (phiA L a) := by
  cases o with
  | fin k =>
    change rt L a (phiA L a) * rt L a (finGL L a _) = rt L a (finGL L a (thetaGL a _ (invT a (Af L) k))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    have h : thetaGL a (conjFin (IsCMField.complexConj L).toRingEquiv) (invT a (Af L) k) =
        PhiU a (Af L) * GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k * (PhiU a (Af L))⁻¹ := by
      change PhiU a (Af L) * invT a (Af L) (GeneralLinearGroup.map _ (invT a (Af L) k)) * (PhiU a (Af L))⁻¹ = _
      rw [invT_map_invT]
    rw [h, phiA, map_mul, map_mul, map_inv, mul_assoc, infGL_comm]
    group
  | cpt k =>
    change rt L a (phiA L a) * rt L a (infGL L a (Unitary.toUnits _)) =
      rt L a (infGL L a (Unitary.toUnits (PhiK L a * barK k * (PhiK L a)⁻¹))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [phiA, map_mul, map_mul, map_inv, toUnits_PhiK, map_mul, map_mul, map_inv]
    have e := infGL_comm (E := L) (a := a) (PhiU a (Cinf L) * Unitary.toUnits (barK k) * (PhiU a (Cinf L))⁻¹)
      (PhiU a (Af L))
    rw [map_mul, map_mul, map_inv] at e
    rw [toUnits_PhiK, ← mul_assoc (_ * _ * _) (finGL L a _), e]
    group
  | lie X =>
    change rt L a (phiA L a) * lie L a (fun i j => star (X i j)) =
      lie L a (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ))) *
        rt L a (phiA L a)
    rw [phiA, map_mul, mul_assoc,
      show (fun i j => star (X i j) : Lie L a) = toL (Matrix.of fun i j => star (X i j)) from rfl,
      GlobalTheory.CapAdInv.rt_lie, ← mul_assoc, ← lie_rt_fin, mul_assoc]
    refine congrArg (fun Y => lie L a (toL Y) * _) ?_
    have h : (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ = -(Matrix.of fun i j => star (X i j)) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    change GlobalTheory.Tw.Phi a (Cinf L) * _ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ = _
    rw [h, mul_neg, neg_mul, neg_neg]

theorem rt_inv_phiA (f : Sm L a) : rt L a (phiA L a)⁻¹ (rt L a (phiA L a) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem dualIsConjBy_of_paired_invT : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  intro L _ _ _ a π ψ ⟨B, hl, hr, hf, hc, hX⟩ ⟨T, hT⟩
  let u : π.V →ₗ[ℂ] π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  have hu : ∀ χ : π.V, (u χ).1 = rt L a (phiA L a) χ.1 := fun χ => by
    change rt L a (finGL L a _) (rt L a (infGL L a (Unitary.toUnits (PhiK L a))) χ.1) = _
    rw [toUnits_PhiK, phiA, map_mul]
    rfl
  have hkey : ∀ o χ, u (π.op (conjOp o) χ) = π.op (thetaOp (invTOp o)) (u χ) := fun o χ =>
    Subtype.ext (by rw [hu, CuspSub.op_val, CuspSub.op_val, hu]; exact LinearMap.congr_fun (rt_phiA_act o) χ.1)
  have hinj : ∀ χ, u χ = 0 → χ = 0 := fun χ h => Subtype.ext (by
    have e := congrArg (fun ξ : π.V => rt L a (phiA L a)⁻¹ ξ.1) h
    simp only [hu, rt_inv_phiA, ZeroMemClass.coe_zero, map_zero] at e
    exact e)
  have hsurj : ∀ χ : π.V, ∃ ξ, u ξ = χ := fun χ =>
    ⟨π.op (.cpt (PhiK L a)⁻¹) (π.op (.fin (PhiU a (Af L))⁻¹) χ), Subtype.ext (by
      rw [hu]
      change rt L a (phiA L a) (rt L a (infGL L a (Unitary.toUnits (PhiK L a)⁻¹)) (rt L a (finGL L a _) χ.1)) = _
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, map_inv, toUnits_PhiK, phiA, map_inv,
        map_inv]
      simp)⟩
  refine ⟨B.compl₂ (T.toLinearMap ∘ₗ u), fun φ h => hl φ fun ψ' => ?_, fun χ h => hinj χ ?_,
    fun k φ χ => ?_, fun k φ χ => ?_, fun X φ χ => ?_⟩
  · obtain ⟨χ, rfl⟩ := T.surjective ψ'
    obtain ⟨ξ, rfl⟩ := hsurj χ
    exact h ξ
  · exact (LinearEquiv.map_eq_zero_iff T).1 (hr _ h)
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hf k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hc k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hX X φ _

end GlobalTheory.ConjDualPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorColumnsIndependentModUniformize
section
open Matrix

namespace GlobalTheory

theorem columns_indepMod :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  intro L _ _ ϖ hϖ n n' x V a H d hd hdiv j
  classical
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hϖi : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc
  have hcint : ∀ k, c k ∈ Formalism.UG.intL L := by
    intro k; simp only [hc]; split_ifs
    · exact mul_mem (hd _) (pow_mem hϖi _)
    · exact zero_mem _
  have hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : 0 < a k
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · obtain ⟨m, hm⟩ : ∃ m, a k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hc, hk, hm]; ring
      · intro b _ hb
        have : k ≠ (b : Fin n) := fun h => hb (Subtype.ext h.symm)
        simp [Pi.single_apply, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc, hk]
      · intro i _
        have : k ≠ (i : Fin n) := fun h => hk (h ▸ i.2)
        simp [Pi.single_apply, this]
  have hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)))) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul]
  have hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L := by
    intro r
    obtain ⟨b, hb, hbe⟩ := hdiv r
    have h1 := congrFun hlin r
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1
    rw [← h1, pow_one] at hbe
    rw [mul_left_cancel₀ hϖ0 hbe]; exact hb
  obtain ⟨b, hb, hbe⟩ := (H c hcint).1 hw j
  refine ⟨b, hb, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := Nat.exists_eq_succ_of_ne_zero j.2.ne'
  simp only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe
  apply mul_right_cancel₀ (pow_ne_zero m hϖ0)
  rw [hbe]; ring

end GlobalTheory
end

