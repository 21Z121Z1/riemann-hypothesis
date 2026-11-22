import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0005
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HermTransversal

theorem isUnit_glue {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ} (e t : ι → R)
    (A : ι → Matrix (Fin n) (Fin n) R) (h1 : ∑ i, e i = 1) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (ht : ∀ i, t i * (A i).det = e i) : IsUnit (∑ i, e i • A i) := by
  classical
  have hee : ∀ i, e i * e i = e i := fun i => by
    have : e i * ∑ j, e j = e i * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_single i (fun j _ hj => ho i j (Ne.symm hj)) (by simp)
    rw [← this, h1, mul_one]
  have hs : ∀ i, e i • (∑ j, e j • A j) = e i • A i := fun i => by
    rw [Finset.smul_sum, Finset.sum_eq_single i]
    · rw [smul_smul, hee]
    · intro j _ hj
      rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
    · simp
  have hB : (∑ i, e i • A i) * (∑ j, (t j * e j) • (A j).adjugate) = 1 := by
    rw [Finset.mul_sum]
    have : ∀ j, (∑ i, e i • A i) * ((t j * e j) • (A j).adjugate) = e j • (1 : Matrix (Fin n) (Fin n) R) := fun j => by
      rw [Matrix.mul_smul, mul_smul, ← Matrix.smul_mul (e j), hs, Matrix.smul_mul, Matrix.mul_adjugate, smul_smul,
        smul_smul]
      congr 1
      rw [mul_right_comm, ht, hee]
    simp only [this]
    rw [← Finset.sum_smul, h1, one_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hB)

section Generic

variable {E R : Type} [Field E] [CharZero E] [CommRing R] {n : ℕ}

theorem exists_herm_notMem (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (ι : E →+* R) (τ : R →+* R)
    (hτι : ∀ z, τ (ι z) = ι (σ z)) (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) (M : Ideal R)
    (hM : M.IsMaximal) :
    ∃ x : Matrix (Fin n) (Fin n) E, (∀ i j, σ (x i j) = x j i) ∧
      (c * x.map ι + d).det * τ (c * x.map ι + d).det ∉ M := by
  letI := Ideal.Quotient.field M
  let π₀ : R →+* R ⧸ M := Ideal.Quotient.mk M
  let φ : E →+* R ⧸ M := π₀.comp ι
  let π := π₀.mapMatrix (m := Fin n)
  let ψ := (π₀.comp τ).mapMatrix (m := Fin n)
  have h1 : π c * π p + π d * π q = 1 := by rw [← map_mul, ← map_mul, ← map_add, h, map_one]
  have h2 : ψ c * ψ p + ψ d * ψ q = 1 := by rw [← map_mul, ← map_mul, ← map_add, h, map_one]
  obtain ⟨y, hy⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h1
  obtain ⟨y', hy'⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h2
  obtain ⟨x, hxs, hx1, hx2⟩ := GlobalTheory.T.exists_hermitian_two_det_ne_zero E (R ⧸ M) σ φ δ hδ hσδ n _ _ _ _ _ _ hy hy'
  have hx : ∀ i j, σ (x i j) = x j i := fun i j => congrFun (congrFun hxs i) j
  refine ⟨x, hx, fun hmem => ?_⟩
  rcases hM.isPrime.mem_or_mem hmem with h' | h'
  · apply hx1
    have e : π₀ (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (π (c * x.map ι + d)).det = 0 at e
    rw [map_add, map_mul] at e
    exact e
  · apply hx2
    have e : (π₀.comp τ) (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (ψ (c * x.map ι + d)).det = 0 at e
    rw [map_add, map_mul] at e
    have e2 : ψ (x.map ι) = x.transpose.map φ := by
      funext i j
      change π₀ (τ (ι (x i j))) = π₀ (ι (x j i))
      rw [hτι, hx]
    rw [e2] at e
    exact e

theorem exists_herm_isUnit_generic {A : Type} [CommRing A] (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (ι : E →+* R) (τ : R →+* R) (hτι : ∀ z, τ (ι z) = ι (σ z)) (hττ : ∀ z, τ (τ z) = z)
    (a : A →+* R) (ha : Function.Injective a) (hτa : ∀ z, τ (a z) = a z) (hfix : ∀ y, τ y = y → ∃ z, a z = y)
    (k : A) (hk : k * 2 = 1)
    (hid : ∀ (κ : Type) [Fintype κ] (f s : κ → A), ∑ i, s i * f i = 1 → ∃ e t : κ → A,
      ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i)
    (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) R, (x.map τ)ᵀ = x ∧ IsUnit (c * x + d) := by
  classical
  let H := {x : Matrix (Fin n) (Fin n) E // ∀ i j, σ (x i j) = x j i}
  let u : H → R := fun x => (c * x.1.map ι + d).det
  let f : H → R := fun x => u x * τ (u x)
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, hx, hn⟩ := exists_herm_notMem σ δ hδ hσδ ι τ hτι c d p q h M hM
    exact hn (hle (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range f) := (Ideal.eq_top_iff_one _).1 htop
  obtain ⟨C, hC⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  have hC' : ∑ i : C.support, C i * f i = 1 := by
    rw [Finset.sum_coe_sort C.support (fun i => C i * f i)]
    exact hC
  have hf : ∀ x, τ (f x) = f x := fun x => by
    simp only [f]
    rw [map_mul, hττ, mul_comm]
  choose g hg using fun x => hfix (f x) (hf x)
  have hs : ∀ x, τ (C x + τ (C x)) = C x + τ (C x) := fun x => by
    rw [map_add, hττ, add_comm]
  choose s hs' using fun x => hfix _ (hs x)
  have h2 : ∑ i : C.support, s i * g i = 2 := by
    apply ha
    have hc := congrArg τ hC'
    rw [map_sum, map_one] at hc
    simp only [map_mul τ, hf] at hc
    rw [map_sum, map_ofNat]
    simp only [map_mul, hg, hs', add_mul]
    rw [Finset.sum_add_distrib, hC', hc, one_add_one_eq_two]
  have h3 : ∑ i : C.support, (k * s i) * g i = 1 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, hk]
  obtain ⟨e, t, he1, heo, het⟩ := hid C.support (fun i => g i) _ h3
  have ha1 : ∑ i, a (e i) = 1 := by rw [← map_sum, he1, map_one]
  refine ⟨∑ i : C.support, a (e i) • i.1.1.map ι, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, hτa, hτι]
    exact Finset.sum_congr rfl fun x _ => by rw [x.1.2]
  · have : c * (∑ i : C.support, a (e i) • i.1.1.map ι) + d =
        ∑ i : C.support, a (e i) • (c * i.1.1.map ι + d) := by
      simp only [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ha1, one_smul, Finset.mul_sum]
      simp only [Matrix.mul_smul]
    rw [this]
    refine isUnit_glue _ (fun i => a (t i) * τ (u i)) _ ha1 (fun i j hij => ?_) (fun i => ?_)
    · rw [← map_mul, heo i j hij, map_zero]
    · rw [← het i, map_mul, hg, mul_assoc, mul_comm (τ (u i))]

end Generic

theorem cA_algebraMap {D : D7} (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.FinTranslate.cA_smul, map_one]

theorem algebraMap_inj {D : D7} : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem half_mul_two {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] :
    algebraMap F A (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F A) 2, ← map_mul]
  simp

theorem exists_herm_isUnit (D : D7) (n : ℕ) (c d p q : Mx D n n) (h : c * p + d * q = 1) :
    ∃ x : Mx D n n, GlobalTheory.MixModel.adj x = x ∧ IsUnit (c * x + d) :=
  exists_herm_isUnit_generic (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (incA D) (cA D) GlobalTheory.DualPairCheck.cA_incA GlobalTheory.DualPairCheck.cA_cA
    (algebraMap (AF D.host.F) (AE D)) algebraMap_inj cA_algebraMap GlobalTheory.DetRootRows.fixed_mem_range
    (algebraMap D.host.F (AF D.host.F) (1 / 2)) half_mul_two (GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' D.host.F) c d p q h

end GlobalTheory.HermTransversal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesRationalDecompositionsOverLoca
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  have hi : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
    obtain ⟨η, hη, h0, h⟩ := exists_idem p
    have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
      refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
      · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        exact TensorProduct.zero_tmul _ _
      · refine Ideal.mem_iInf.2 fun w => ?_
        change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        rw [h0 w.1 w.2, TensorProduct.zero_tmul]
    have := pr_int p (hU.1 _ hm).2.2
    rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this
  have h0 : D.host.xi0 ≠ 0 := fun h => by
    have := GlobalTheory.MixModel.HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
    rw [h, map_zero, zero_mul] at this
    have h2 := congrArg p.pr this
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have a := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral p hU)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D D.host.xi0)) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

theorem val_star_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D (star D.host.xi0))) = 1 := by
  rw [Brg.star_purely_imaginary_eq_neg, map_neg, map_neg, Valuation.map_neg, val_xi p hU]

theorem val_nat (p : SplitPt D k) {PP : Pl D.host.E} (hI : Formalism.L2.NTheta.IsIdemAt p.e PP) (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : valuation k (p.pr (incA D (n : D.host.E))) = 1 := by
  have hx : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hn (h ▸ PP.asIdeal.zero_mem)
  have h1 := (hI.2 _ hx).not.1 hn
  rw [not_not] at h1
  have hcast : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := by simp
  rw [hcast] at h1
  have hi : p.pr (incA D (n : D.host.E)⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact h1
  have hn0 : (n : D.host.E) ≠ 0 := by
    intro h; apply hx; exact_mod_cast (by rw [hcast]; exact h : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = 0)
  have a : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1 := by
    rw [map_natCast, map_natCast]
    exact (Valuation.mem_integer_iff _ _).1 (natCast_mem _ n)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D (n : D.host.E))) * valuation k (p.pr (incA D (n : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hn0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D (n : D.host.E))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tau_norm {a : XGeo D} (y : YRat a) {lam : D.host.E} (hT : y.Tau lam) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    star lam * (lam * (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ)) =
      -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
  obtain ⟨h1, h2⟩ := hT j h
  have h3 := congrArg (fun A => star a.ζ₀ ⬝ᵥ A *ᵥ a.ζ₀) h1
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul] at h3
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h2, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h3
  rw [← h3]; ring

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_hz {a : XGeo D} (y : YRat a) (q : SplitPt D k) (hU : q.UnitAA) {PP : Pl D.host.E}
    (hI : Formalism.L2.NTheta.IsIdemAt q.e PP) (n : ℕ) (hT : y.Tau (-D.host.xi0 ^ (D.R.m / 2)))
    (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E)) (hnP : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∀ ρ j (h : j + 2 * ρ + 2 = D.R.m), valuation k ((ofSplit q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1 := by
  have hx := val_xi q hU
  have hs := val_star_xi q hU
  have hN := val_nat q hI n hnP
  intro ρ
  induction ρ with
  | zero =>
    intro j h
    change valuation k (q.pr (incA D (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ))) = 1
    have h3 := congrArg (fun x => valuation k (q.pr (incA D x))) (tau_norm y hT j h)
    simp only [hn, map_mul, map_neg, map_pow, Valuation.map_neg, Valuation.map_pow, star_neg, star_pow, hx, hs, hN,
      one_pow, one_mul, mul_one] at h3
    exact h3
  | succ σ ih =>
    intro j h
    have h1 := (y.lnk j σ h).norm
    change star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ = _ at h1
    change valuation k (q.pr (incA D (star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))) = 1
    rw [h1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hx, hs, one_mul, one_mul]
    exact ih _ _

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

theorem normalFrames_exist : ∀ {D : D7} (a : XGeo D) (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (n : ℕ), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
    star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E) → ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
    ∃ (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc := by
  intro D a y βT PP l n hT hn hnP
  have hxi : (ofSplit l.q).xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne (ofSplit l.q)
  have hv : valuation l.k (ofSplit l.q).xi = 1 := val_xi l.q l.unit
  have hsc : ∀ j, (ofSplit l.q).xi ^ (j / 2) ≠ 0 := fun j => pow_ne_zero _ hxi
  have hz := val_hz y l.q l.unit l.idem n hT hn hnP
  have hm := l.hs
  obtain ⟨r, hr⟩ := D.R.m_even
  have key : ∀ j c (hc : j + c = l.s + 1), ∃ F : Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) ((ofSplit l.q).xi ^ (j / 2))
        (l.FX j (by omega)) F) ∧
      ∀ j' (hj : j = j' + 1) ρ h, (ofSplit l.q).IsJacFrame ((y.jac j' ρ h).lev (a.x (j' + 1)).vol)
        ((ofSplit l.q).xi ^ (j' / 2)) ((ofSplit l.q).hz ((y.bes j' ρ h).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
        (hj ▸ F) := by
    intro j c hc
    by_cases hE : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hE
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_bes (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol) (hsc j)
        (l.FX j (by omega))
      obtain rfl : c = 2 * ρ + 1 := by omega
      refine ⟨F, fun ρ' h' => ?_, fun j' hj ρ' h' => absurd h' (by omega)⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
    · have hE' : ∀ ρ, j + 2 * ρ + 2 ≠ D.R.m := fun ρ h => hE ⟨ρ, h⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hE' (r - 1); omega⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ, j' + 2 * ρ + 2 = D.R.m := ⟨(D.R.m - j' - 2) / 2, by have := hE' ((D.R.m - j' - 3) / 2); omega⟩
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_jac (ofSplit l.q) ((y.jac j' ρ hρ).lev (a.x (j' + 1)).vol) (hsc j')
        (GlobalTheory.LocMod.Witness.hz_ne (ofSplit l.q) ((y.bes j' ρ hρ).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
      obtain rfl : c = 2 * ρ := by omega
      refine ⟨F, fun ρ' h' => absurd h' (hE' ρ'), fun j'' hj ρ' h' => ?_⟩
      obtain rfl : j'' = j' := by omega
      obtain rfl : ρ' = ρ := by omega
      exact hF
  refine ⟨fun j c hc => (key j c hc).choose, fun j => (ofSplit l.q).xi ^ (j / 2), fun j => ?_, fun j => ?_,
    fun j ρ h => hz ρ j h, fun j ρ h c hc => (key j c hc).choose_spec.1 ρ h,
    fun j ρ h c hc => (key (j + 1) c hc).choose_spec.2 j rfl ρ h, fun h => ?_⟩
  · rw [map_pow, hv, one_pow]
  · show (ofSplit l.q).xi ^ ((j + 1 + 1) / 2) = (ofSplit l.q).xi ^ (j / 2) * (ofSplit l.q).xi
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]
  · have h2 := (hT l.s h).2
    funext i
    have e1 : ((y.τ l.s h).map (ofSplit l.q).pr *ᵥ fun i => (ofSplit l.q).pr (a.ζ₀ i)) i =
        GlobalTheory.LocMod.Witness.prH (ofSplit l.q) ((y.τ l.s h *ᵥ a.ζ₀) i) :=
      (RingHom.map_mulVec (GlobalTheory.LocMod.Witness.prH (ofSplit l.q)) _ _ i).symm
    rw [e1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_neg, map_pow]
    change -((ofSplit l.q).xi ^ (D.R.m / 2)) * (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i) = _
    rw [show D.R.m / 2 = l.s / 2 + 1 by omega, pow_succ]
    ring

end GlobalTheory.Fam.FramesY
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulAnnihilatorHalfMemStandardHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfAnnStd

variable {D : D7}

theorem symplO_nsmul_swap (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.PlaceModel.symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem exists_nsmul_frame_mem (S T : HSp D) : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) (fun _ => True), N • y ∈ stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S).1.fg (GlobalTheory.PlaceModel.isSelfDualC_latFrame T).1.fg
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem exists_nsmul_ann_mem_stdHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ N : ℕ, 0 < N ∧ ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → N • u ∈ stdHom S T := by
  intro D ψ hψ S T Q e he
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_frame_mem S T
  refine ⟨N * N, Nat.mul_pos hN hN, fun u hu hann => ?_⟩
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.AnnihBox.infPart_cA' e (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hfix : cA D e • u = u := Matrix.ext fun i j => hu i j
  have hall : ∀ x ∈ stdHom S T, ψ (symplO S T x u) = 1 := fun x hx => by
    have h := hann (e • x) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hx) fun i j => by
        change e * (e * _) = e * _
        rw [← mul_assoc, hee]
    rwa [GlobalTheory.PlaceModel.symplO_smul, hfix] at h
  rw [mul_smul]
  refine hNm _ (((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1 _ (Matrix.ext fun i j => ?_)).2 fun y hy => ?_)
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, ← hu i j, RingHom.map_mul, hinf, zero_mul,
      mul_zero, Matrix.zero_apply]
  · rw [symplO_nsmul_swap, GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hall _ (hNm y hy), inv_one]

end GlobalTheory.HalfAnnStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDLatY

theorem exists_selfDual_latY : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  intro D L hT Gi Gl Kc Yd cX ex W hp j hj
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  exact ⟨(pk W).ΛY j, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D (Yc D j) ((pk W).βY j) ((pk W).ΛY j) _ (hC.lev.βY j hj)⟩

end GlobalTheory.SDLatY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_pureTensorO_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  first | exact @GlobalTheory.AdForm.FinComm.finite_comm_creation | exact GlobalTheory.AdForm.FinComm.finite_comm_creation | (intros; apply GlobalTheory.AdForm.FinComm.finite_comm_creation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.Unf

theorem flatFun_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∀ K : Set (GA D V × GA D W), IsCompact K → ∃ M : UX D ρ → ℝ, Integrable M vU.ν ∧ ∀ p ∈ K, ∀ y w u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (om p Φ) w u‖ ≤ M u := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hW vU x hx Φ hΦ K hK
  have hn : ∀ a, ‖ψ a‖ = 1 := hW.std.1.2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨K', hK', hC⟩ := GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant D ψ V W χV χW om hW θ hθ V₀ ρ dV vS Φ hΦ K hK
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular D θ hθ W.rank ρ vU x hx
  obtain ⟨C, hC⟩ := hC N
  refine ⟨fun u => C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1), (hN K' hK').const_mul C, ?_⟩
  intro p hp y w u
  have hT := vT.covol
  unfold flatFun evalAt
  rw [norm_mul, norm_star]
  have h1 : ‖psiUni ψ u.1‖ = 1 := hn _
  rw [h1, one_mul]
  unfold GlobalTheory.MixModel.HypDec.mixT
  have hb : ∀ ξ ∈ vT.𝓕, ‖heisO ψ V₀ W (dW.incX V₀ ξ) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w)
      (dV.mixS W ψ vS.μ vS.𝓕 (om p Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1)))) 0‖ ≤ C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1) := by
    intro ξ _
    rw [dW.integrandT_eq, norm_mul, hn, one_mul]
    exact hC p hp _ _
  have := norm_setIntegral_le_of_norm_le_const (by rw [hT.2.2]; exact ENNReal.one_lt_top) hb
  rw [measureReal_def, hT.2.2, ENNReal.toReal_one, mul_one] at this
  exact this
end GlobalTheory.Unf
end
end

