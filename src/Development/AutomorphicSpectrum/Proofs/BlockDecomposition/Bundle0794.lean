import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0792
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanVolumeRankOneIsotropicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_volume_rank_one_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) (m : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) = ENNReal.ofReal (D (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwist
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_tw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ)
    (U U' : Submodule ℂ (Sm E N)) (z : ℂ) (h : Carries e U U') : Carries e (tw U z) (tw U' z) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', hx⟩ := h ψ hψ
  refine ⟨mulChi N (Model.absC E z) ψ', ⟨ψ', hψ', rfl⟩, fun x => ?_⟩
  simp only [LinearEquiv.coe_coe, mulChi_apply, hx, mul_assoc]

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacter
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_absFn_tw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z z' : ℂ) : Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  rintro φ ⟨ψ, hψ, rfl⟩
  refine ⟨mulChi N (GlobalTheory.CuspRep.Model.absC E z') ψ, ⟨ψ, hψ, rfl⟩, fun x => ?_⟩
  have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
      Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
  simp only [LinearEquiv.coe_coe, mulChi_apply, absFn]
  rw [e z', e (z' - z), e z, mul_left_comm, ← Complex.exp_add, ← add_mul, sub_add_cancel]

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperators
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.CapCoeff

theorem coeff_mem_of_values {A : Type} [AddCommGroup A] [Module ℂ A] (W : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range n, u ^ k • c k ∈ W) : ∀ k < n, c k ∈ W := by
  intro k hk
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  let p : ℂ[X] := ∑ i ∈ Finset.range n, Polynomial.C (f (Submodule.Quotient.mk (c i))) * Polynomial.X ^ i
  have hp : p = 0 := by
    refine Polynomial.funext fun u => ?_
    have h0 : (Submodule.Quotient.mk (∑ i ∈ Finset.range n, u ^ i • c i) : A ⧸ W) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).2 (h u)
    have h1 := congrArg f h0
    rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h1
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have hc := congrArg (fun q : ℂ[X] => q.coeff k) hp
  simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range, hk] using hc

theorem qdet_coeffs {A : Type} [Ring A] [Algebra ℂ A] (W : Subalgebra ℂ A) (m : ℕ)
    (X : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ) (hW : ∀ u, Formalism.REAL.qdet X u ∈ W) :
    ∃ (c : ℕ → A) (t : ℂ), (∀ k, c k ∈ W) ∧ c (m + 1) = 1 ∧ c m = ∑ i, X i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.CapelliNext.qdet_shift_next_coeff A m X s
  have hm : ∀ k < m + 1 + 1, c k ∈ Subalgebra.toSubmodule W :=
    coeff_mem_of_values _ _ c fun u => by
      rw [← h3 u]
      exact hW _
  refine ⟨fun k => if k < m + 1 + 1 then c k else 0, t, fun k => ?_, ?_, ?_, fun u => ?_⟩
  · by_cases hk : k < m + 1 + 1
    · simp only [if_pos hk]
      exact hm k hk
    · simp only [if_neg hk]
      exact W.zero_mem
  · simpa only [if_pos (Nat.lt_succ_self (m + 1))] using h1
  · simpa only [if_pos (show m < m + 1 + 1 by omega)] using h2
  · rw [h3 u]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [if_pos (Finset.mem_range.1 hk)]

theorem qdet_commute_of {A : Type} [Ring A] [Algebra ℂ A] {n p : ℕ} (X : Fin n → Fin n → A) (Y : Fin p → Fin p → A)
    (h : ∀ i j k l, X i j * Y k l = Y k l * X i j) (u v : ℂ) :
    Formalism.REAL.qdet X u * Formalism.REAL.qdet Y v = Formalism.REAL.qdet Y v * Formalism.REAL.qdet X u := by
  have h1 : Formalism.REAL.qdet X u ∈ Subalgebra.centralizer ℂ (Set.range fun kl : Fin p × Fin p => Y kl.1 kl.2) := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (h i j kl.1 kl.2).symm
  have h2 : Formalism.REAL.qdet Y v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X)
    (u v : ℂ) : Formalism.REAL.qdet X u * Formalism.REAL.qdet X v = Formalism.REAL.qdet X v * Formalism.REAL.qdet X u := by
  have h : Formalism.REAL.qdet X v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun c d => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact Formalism.REAL.qDetCentral A n X hX u c d
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h _ rfl

theorem glRel_comp {A : Type} [Ring A] {n p : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {f : Fin p → Fin n}
    (hf : Function.Injective f) : Formalism.REAL.GlRel fun i j => X (f i) (f j) := by
  intro a b c d
  have h := hX (f a) (f b) (f c) (f d)
  simpa only [hf.eq_iff] using h

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem Eop_mem_of_lie {N : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E N))) (hL : ∀ X, lie E N X ∈ S) (τ : E →+* ℂ)
    (p q : Fin N) : Eop τ p q ∈ S :=
  Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hL _) (Subalgebra.smul_mem _ (hL _) _)) _

def gens (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Set (Module.End ℂ (Sm E (r + s))) :=
  Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capR r s p.1 p.2) ∪
    Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capS r s p.1 p.2)

def capAlg (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) :
    Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) :=
  Algebra.adjoin ℂ (gens E r s)

theorem capR_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capR r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inl ⟨(τ, u), rfl⟩)

theorem capS_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capS r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inr ⟨(τ, u), rfl⟩)

theorem capR_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  by_cases h : τ = τ'
  · subst h
    exact (GlobalTheory.CompanionTheory.CTFin.CapFactor.capR_commute_capS r s τ u v).eq
  · unfold GlobalTheory.CompanionTheory.CTFin.capR GlobalTheory.CompanionTheory.CTFin.capS
    exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capR_mul_capR (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capR r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capR r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capR
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.castAdd_injective r s)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capS_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capS r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capS r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capS
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.natAdd_injective s r)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem gens_comm (r s : ℕ) : ∀ a ∈ gens E r s, ∀ b ∈ gens E r s, a * b = b * a := by
  rintro a (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩) b (⟨⟨τ', v⟩, rfl⟩ | ⟨⟨τ', v⟩, rfl⟩)
  · exact capR_mul_capR r s _ _ _ _
  · exact capR_mul_capS r s _ _ _ _
  · exact (capR_mul_capS r s _ _ _ _).symm
  · exact capS_mul_capS r s _ _ _ _

theorem capAlg_comm (r s : ℕ) : ∀ x ∈ capAlg E r s, ∀ y ∈ capAlg E r s, x * y = y * x := by
  intro x hx y hy
  letI := Algebra.adjoinCommRingOfComm ℂ (gens_comm (E := E) r s)
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin ℂ (gens E r s)) ⟨y, hy⟩)

theorem capAlg_le (r s : ℕ) (T : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))))
    (hT : ∀ τ p q, Eop (a := r + s) τ p q ∈ T) : capAlg E r s ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩)
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _

theorem capAlg_commute_cap (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (τ : E →+* ℂ) (u : ℂ) :
    Commute (cap (a := r + s) τ u) x := by
  have hc : capAlg E r s ≤ Subalgebra.centralizer ℂ {cap (a := r + s) τ u} := by
    refine capAlg_le r s _ fun τ' p q => Eop_mem_of_lie _ (fun X => ?_) τ' p q
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (commute_cap_lie τ u X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hc hx) _ rfl

theorem capR_coeffs (m s : ℕ) (τ : E →+* ℂ) :
    ∃ (c : ℕ → Module.End ℂ (Sm E (m + 1 + s))) (t : ℂ),
      (∀ k, c k ∈ capAlg E (m + 1) s) ∧ c (m + 1) = 1 ∧
      c m = ∑ i : Fin (m + 1), Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t • 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capR (m + 1) s τ (u - (s : ℂ) / 2) =
        ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, h2, h3⟩ := qdet_coeffs (capAlg E (m + 1) s) m
    (fun i j : Fin (m + 1) => Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
    ((s : ℂ) / 2 - (((m + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capR_mem (E := E) (m + 1) s τ (u - (((m + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capR, sub_add_cancel] at this)
  refine ⟨c, t, h0, h1, h2, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capR]
  congr 1
  ring

theorem capS_coeffs (r n : ℕ) (τ : E →+* ℂ) :
    ∃ c : ℕ → Module.End ℂ (Sm E (r + (n + 1))),
      (∀ k, c k ∈ capAlg E r (n + 1)) ∧ c (n + 1) = 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capS r (n + 1) τ (u + (r : ℂ) / 2) =
        ∑ k ∈ Finset.range (n + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, -, h3⟩ := qdet_coeffs (capAlg E r (n + 1)) n
    (fun i j : Fin (n + 1) => Eop (a := r + (n + 1)) τ (Fin.natAdd r i) (Fin.natAdd r j))
    (-((r : ℂ) / 2) - (((n + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capS_mem (E := E) r (n + 1) τ (u - (((n + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capS, sub_add_cancel] at this)
  refine ⟨c, h0, h1, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capS]
  congr 1
  ring

theorem leftInv_closure {N r : ℕ} (F : Sm E N)
    (hF : ∀ (v : BlockIx N r → Ad E) (g : GA E N), F.1 (unip v * g) = F.1 g) :
    ∀ w ∈ Subgroup.closure (Set.range (unip : (BlockIx N r → Ad E) → GA E N)), ∀ g, F.1 (w * g) = F.1 g := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact hF v
  | one => intro g; rw [one_mul]
  | mul x y _ _ hx hy => intro g; rw [mul_assoc, hx, hy]
  | inv x _ hx => intro g; rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

theorem capAlg_leftInv (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (F : Sm E (r + s))
    (hF : ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g)
    (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)) : (x F).1 (unip v * g) = (x F).1 g := by
  have hc := capAlg_le (E := E) r s (GlobalTheory.SpehInfChar.leftInvAlg (Subgroup.closure
    (Set.range (unip : (BlockIx (r + s) r → Ad E) → GA E (r + s)))))
    (fun τ p q => GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ p q)
  exact hc hx F (leftInv_closure F hF) (unip v) (Subgroup.subset_closure ⟨v, rfl⟩) g

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  intro E _ _ _ r s hr hs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  choose a t ha0 ha1 ha2 ha3 using capR_coeffs (E := E) m (n + 1)
  choose b hb0 hb1 hb2 using capS_coeffs (E := E) (m + 1) n
  exact ⟨capAlg E (m + 1) (n + 1), a, b, t, capAlg_comm _ _, fun x hx τ u => capAlg_commute_cap _ _ hx τ u,
    fun x hx F hF v g => capAlg_leftInv _ _ hx F hF v g, ha0, hb0, ha1, hb1, ha2, ha3, hb2⟩

end GlobalTheory.CompanionTheory.CapCoeff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompact
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF.Tails

theorem linearIndependent_tails {K : Type} [CommRing K] {M n : ℕ} {Y : Fin (n + 1) → Fin (M + 1) → K}
    (hY : LinearIndependent K Y) (h0 : ∀ i : Fin M, Y 0 i.succ = 0) :
    LinearIndependent K (fun (j : Fin n) (i : Fin M) => Y j.succ i.succ) := by
  have hfree := Fintype.linearIndependent_iff.1 hY

  have hnzd : ∀ b : K, b * Y 0 0 = 0 → b = 0 := by
    intro b hb
    have hsum : ∑ i, (Pi.single 0 b : Fin (n + 1) → K) i • Y i = 0 := by
      rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 1)) (Finset.mem_univ _)
        (fun i _ hi => by simp [Pi.single_eq_of_ne hi])]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb
      · simp [h0 i]
    simpa using hfree _ hsum 0
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have hw' : ∀ i : Fin M, ∑ j, w j * Y j.succ i.succ = 0 := by
    intro i
    have := congrFun hw i
    simpa [Finset.sum_apply] using this
  set r : K := ∑ j, w j * Y j.succ 0 with hr
  have hsum : ∑ i, (Fin.cons (-r) (fun j => Y 0 0 * w j) : Fin (n + 1) → K) i • Y i = 0 := by
    rw [Fin.sum_univ_succ]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply]
      have h1 : ∑ j, Y 0 0 * w j * Y j.succ 0 = r * Y 0 0 := by
        rw [hr, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      ring
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply, h0 i, mul_zero, zero_add]
      have : ∑ j, Y 0 0 * w j * Y j.succ i.succ = Y 0 0 * ∑ j, w j * Y j.succ i.succ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hw' i, mul_zero]
  have hj := hfree _ hsum j.succ
  rw [Fin.cons_succ] at hj
  exact hnzd _ (by rw [mul_comm]; exact hj)

theorem exists_compact_tails (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ)
    (Q : Set (Fin (n + 1) → Fin (M + 1) → K)) (hQ : IsCompact Q)
    (hfree : ∀ Y ∈ Q, LinearIndependent K Y) :
    ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧
      ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  let tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K := fun Y j i => Y j.succ i.succ
  have htl : Continuous tl :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply i.succ).comp (continuous_apply j.succ)
  have hclosed : IsClosed {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} := by
    have : {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} =
        ⋂ i : Fin M, {Y | Y 0 i.succ = 0} := by
      ext Y
      simp
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i.succ).comp (continuous_apply 0)) continuous_const
  refine ⟨tl '' (Q ∩ {Y | ∀ i : Fin M, Y 0 i.succ = 0}), (hQ.inter_right hclosed).image htl, ?_, ?_⟩
  · rintro _ ⟨Y, ⟨hYQ, h0⟩, rfl⟩
    exact linearIndependent_tails (hfree Y hYQ) h0
  · intro A c X h
    exact ⟨vec A c X, ⟨h, fun i => by simp [vec]⟩, by funext j i; simp [tl, vec]⟩

end GlobalTheory.CompanionTheory.SW.StageF.Tails
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSet
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem exists_finset_separating_points {A : Type} (W : Submodule ℂ (A → ℂ)) :
    FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 :=
  _root_.Bl.FirstLemmaH.goal1 W

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStableStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_dim_compact_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) → ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧ (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧ ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | exact GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | (intros; apply GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetIntOff
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

variable {D : D7} {a b c : ℕ}

theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem intOff_mm {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := by
  intro v hv i j
  have h : mm x y i j = ∑ k, x i k * y k j := Matrix.mul_apply
  have hs : ∑ k, x i k * y k j ∈ (intLoc D.host.F D.host.E v).comap (cv D v) :=
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (Subring.mem_comap.2 (hx v hv i k))
      (Subring.mem_comap.2 (hy v hv k j))
  rw [h]
  exact Subring.mem_comap.1 hs

theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := by
  intro v hv i j
  have h : adj x i j = cA D (x j i) := rfl
  rw [h, cv_cA]
  exact sigR_mem_intLoc _ (hx v hv j i)

theorem exists_finset_intOff (x : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S x := by
  have hbad : {v : Pl D | ¬ ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v}.Finite :=
    GlobalTheory.CompanionTheory.ColumnSplitting.exists_intOff x
  refine ⟨hbad.toFinset, fun S hS v hv => ?_⟩
  by_contra hc
  exact hv (hS (hbad.mem_toFinset.2 hc))

theorem intOff_yv (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : Mx D V.rank r × Mx D V.rank t,
      IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z) := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_finset_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS z hz₁ hz₂ => ?_⟩
  exact intOff_mm (h₁ S (Finset.union_subset_left hS))
    (intOff_mm (intOff_adj hz₁) (intOff_mm (h₂ S (Finset.union_subset_right hS)) hz₂))

end GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjectionStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | exact GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | (intros; apply GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_discrete_spectrum : PositivityTheory.Rg.BcB.F.F5.FinDiscN := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscN.finDiscN | exact GlobalTheory.CompanionTheory.FinDiscN.finDiscN | (intros; apply GlobalTheory.CompanionTheory.FinDiscN.finDiscN <;> assumption)
end

