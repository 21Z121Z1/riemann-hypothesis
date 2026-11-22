import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => MvPolynomial.coeff m (F k)

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finset_sum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finset_sum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, MvPolynomial.coeff (e i) P • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => MvPolynomial.coeff (d : σ →₀ ℕ) P •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => MvPolynomial.coeff (e i) (ρ k φ),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => MvPolynomial.coeff (e i) (ρ k₀ (MvPolynomial.monomial (e j) 1)),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]
  simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnIdent

variable {D : D7}

theorem uj_neg_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (-J) * (g : Matrix (Fin n) (Fin n) A) = -J ↔
    Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uh_neg_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem gramAt_neg_eq (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem mem_GQ_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V := by
  cases ε
  · exact Iff.rfl
  · constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq]; exact hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq] at hx; exact hx, e⟩

theorem mem_GfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V := Iff.rfl

theorem mem_GinfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V :=
  Iff.rfl

theorem uh_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  cases ε
  · rfl
  · rw [gramAt_neg_eq, uh_neg_eq]

theorem lieAt_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) : lieAt (sgn ε V) τ = lieAt V τ := by
  cases ε
  · rfl
  · ext X
    show Xᴴ * gramAt D (neg V) τ + gramAt D (neg V) τ * X = 0 ↔ Xᴴ * gramAt D V τ + gramAt D V τ * X = 0
    rw [gramAt_neg_eq, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

theorem isAtTau_sgn (θ : InfFam D) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (sgn ε V)) : IsAtTau θ (sgn ε V) τ g x ↔ IsAtTau θ V τ g (ofSgn ε V x) := Iff.rfl

theorem atTau_sgn (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g := by
  by_cases h : ∃ x, IsAtTau θ V τ g x
  · have h₁ : ∃ x, IsAtTau θ (sgn ε V) τ g x := by
      obtain ⟨x, hx⟩ := h
      refine ⟨(ofSgn ε V).symm x, (isAtTau_sgn θ ε V τ g _).2 ?_⟩
      rw [MulEquiv.apply_symm_apply]; exact hx
    have a : IsAtTau θ (sgn ε V) τ g (atTau θ (sgn ε V) τ g) := by
      unfold atTau; rw [dif_pos h₁]; exact h₁.choose_spec
    have b : IsAtTau θ V τ g (atTau θ V τ g) := by
      unfold atTau; rw [dif_pos h]; exact h.choose_spec
    exact GlobalTheory.Published.AutFin.Model.isAtTau_unique θ V hθ ((isAtTau_sgn θ ε V τ g _).1 a) b
  · have h₁ : ¬ ∃ x, IsAtTau θ (sgn ε V) τ g x := fun ⟨x, hx⟩ => h ⟨_, (isAtTau_sgn θ ε V τ g x).1 hx⟩
    have a : atTau θ (sgn ε V) τ g = 1 := by unfold atTau; rw [dif_neg h₁]
    have b : atTau θ V τ g = 1 := by unfold atTau; rw [dif_neg h]
    rw [a, b, map_one]

theorem meas_sgn (ε : Bool) (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν := by
  obtain ⟨-, -, -, hb, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, -, -, hb₁, hg₁, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (sgn ε V)
  let h : GA D (sgn ε V) ≃ₜ GA D V :=
    { toEquiv := (ofSgn ε V).toEquiv, continuous_toFun := continuous_ofSgn ε V,
      continuous_invFun := continuous_ofSgn_symm ε V }
  have me : MeasurableEmbedding (ofSgn ε V) := h.toMeasurableEquiv.measurableEmbedding
  have hm : Measurable (ofSgn ε V) := (continuous_ofSgn ε V).measurable
  have hm' : Measurable (ofSgn ε V).symm := (continuous_ofSgn_symm ε V).measurable
  have mp : MeasurePreserving (ofSgn ε V) (ν.map (ofSgn ε V).symm) ν := by
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm hm']
    have : (⇑(ofSgn ε V) ∘ ⇑(ofSgn ε V).symm) = id := funext fun x => (ofSgn ε V).apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨ν.map (ofSgn ε V).symm,
    (ofSgn ε V).symm.isHaarMeasure_map ν (continuous_ofSgn_symm ε V) (continuous_ofSgn ε V), ?_, fun φ => ?_⟩
  · refine h𝓕.preimage_of_equiv mp.quasiMeasurePreserving
      (e := fun γ : GQ V => (⟨(ofSgn ε V).symm γ, (mem_GQ_sgn ε V _).2 (by rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩ :
        GQ (sgn ε V))) ⟨fun a b hab => ?_, fun δ => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((ofSgn ε V).symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ofSgn ε V δ, (mem_GQ_sgn ε V δ).1 δ.2⟩, Subtype.ext ((ofSgn ε V).symm_apply_apply δ)⟩
    · show ofSgn ε V ((ofSgn ε V).symm (γ : GA D V) * x) = (γ : GA D V) * ofSgn ε V x
      rw [map_mul, MulEquiv.apply_symm_apply]
  · exact ⟨mp.integrableOn_comp_preimage me, mp.setIntegral_preimage_emb me φ 𝓕⟩

theorem sgnLaw_holds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V :=
  fun _ θ hθ ε V => ⟨mem_GQ_sgn ε V, mem_GfC_sgn ε V, mem_GinfC_sgn ε V, uh_sgn ε V, lieAt_sgn ε V,
    fun τ g => atTau_sgn θ hθ ε V τ g, fun ν 𝓕 hν h𝓕 => meas_sgn ε V ν 𝓕 hν h𝓕⟩

end GlobalTheory.SgnIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceModelOnto

variable {D : D7}

theorem isSBHalf_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem isSBHalf_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem isSBHalf_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem placeModel_onto_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first
  | exact @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | (apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local ..)

end GlobalTheory.PlaceModelOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatticeHalves

theorem splitLattice : ∀ D : D7, SplitLattice D := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨a, haA, ha0, hmax⟩, ⟨b, hbA, hb0, hbmax⟩⟩ := GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate D v φ e he
  refine ⟨⟨a, haA, ha0, hmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩,
    ⟨b, hbA, hb0, hbmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceHomLattice_entries_bounded_by_idealValuation D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.splitPlaceBoundedMatrix_from_halfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceAdjointMatrix_homLattice_bounded_conjugateIdeal D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbA hb0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩

end GlobalTheory.SplitLatticeHalves
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped ENNReal

namespace GlobalTheory.Size.SupWord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {f f' : WO V W → ℂ}
  {p : (WO V W → ℂ) → ℝ≥0∞}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    wordAct (heisDer ψ θ) l (f + f') = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem word_smul (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) (c : ℂ) (f : WO V W → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem ws_add_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (k : ℕ) :
    wordSum (heisDer ψ θ) p k (f + f') ≤ wordSum (heisDer ψ θ) p k f + wordSum (heisDer ψ θ) p k f' :=
  wordSum_le_add fun l => by rw [word_add hψ hθ l h h']; exact hp _ _

theorem ws_smul (hp : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (k : ℕ) (c : ℂ) (f : WO V W → ℂ) :
    wordSum (heisDer ψ θ) p k (c • f) = ‖c‖ₑ * wordSum (heisDer ψ θ) p k f :=
  wordSum_eq_mul fun l => by rw [word_smul]; exact hp _ _

theorem ws_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (∑ i ∈ s, g i) ≤ ∑ i ∈ s, wordSum (heisDer ψ θ) p k (g i) := by
  refine Finset.le_sum_of_subadditive_on_pred (wordSum (heisDer ψ θ) p k) (IsThetaFunO ψ V W) ?_
    (fun _ _ a b => ws_add_le hψ hθ hp a b k) (fun _ _ => theta_add) g hg
  have := ws_smul (ψ := ψ) (θ := θ) hs k 0 (0 : WO V W → ℂ)
  rw [zero_smul, enorm_zero, zero_mul] at this
  simp [this]

theorem ws_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * wordSum (heisDer ψ θ) p (k + 1) f := by
  have ht : ∀ (c : ℂ) a, IsThetaFunO ψ V W (c • heisDer ψ θ a f) := fun c a =>
    theta_smul c (theta_dRho hθ hψ a.1 _ hf)
  have hb : ∀ (c : ℝ) a, wordSum (heisDer ψ θ) p k ((c : ℂ) • heisDer ψ θ a f) ≤
      ENNReal.ofReal |c| * wordSum (heisDer ψ θ) p (k + 1) f := fun c a => by
    rw [ws_smul hs, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact wordSum_letter_le k a f
  rw [dRho_eq_sum_heisDer hψ hθ hf, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun i _ => theta_finsetSum _ fun j _ => theta_add (ht _ _) (ht _ _)) k).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun j _ => theta_add (ht _ _) (ht _ _)) k).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_mul]
  exact (ws_add_le hψ hθ hp (ht _ _) (ht _ _) k).trans (add_le_add (hb _ _) (hb _ _))

theorem supN_add_le (g g' : WO V W → ℂ) : (⨆ w, ‖(g + g') w‖ₑ) ≤ (⨆ w, ‖g w‖ₑ) + ⨆ w, ‖g' w‖ₑ :=
  iSup_le fun w => (enorm_add_le (g w) (g' w)).trans (add_le_add (le_iSup (fun w => ‖g w‖ₑ) w)
    (le_iSup (fun w => ‖g' w‖ₑ) w))

theorem supN_smul (c : ℂ) (g : WO V W → ℂ) : (⨆ w, ‖(c • g) w‖ₑ) = ‖c‖ₑ * ⨆ w, ‖g w‖ₑ := by
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]

theorem wordSum_sup_sub_and_derAlong :
    ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  intro D V W ψ hψ θ hθ
  have ha : ∀ g g' : WO V W → ℂ, (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g' := supN_add_le
  have hs : ∀ (c : ℂ) (g : WO V W → ℂ), (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g := supN_smul
  refine ⟨fun G H c k hG hH => ?_, fun r C x => ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul]
    refine (ws_add_le hψ hθ ha hG (theta_smul _ hH) k).trans ?_
    rw [ws_smul hs, enorm_neg]
  · refine ⟨∑ τ, ∑ i, ∑ j, (|(dirAt V W C τ (x.map (tauE D τ)) i j).re| +
      |(dirAt V W C τ (x.map (tauE D τ)) i j).im|), by positivity, fun G hG k => ?_⟩
    unfold derAlong
    refine (ws_sum_le hψ hθ ha hs _ (fun τ _ => theta_dRho hθ hψ τ _ hG) k).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => by positivity), Finset.sum_mul]
    exact Finset.sum_le_sum fun τ _ => ws_dRho_le hψ hθ ha hs hG τ _ k

end GlobalTheory.Size.SupWord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormIsotropicPartAddMiddlePartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_isotropicPart_add_middlePart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  first | exact @GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | exact GlobalTheory.TowerForm.symplOH_isoPart_add_midPart | (intros; apply GlobalTheory.TowerForm.symplOH_isoPart_add_midPart <;> assumption)
end

