import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBoxStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_by_small_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainBoundStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_fundamental_domain_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Conc.smNear | exact GlobalTheory.CompanionTheory.Conc.smNear | (intros; apply GlobalTheory.CompanionTheory.Conc.smNear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingLipschitzBoundStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_lipschitz_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  first | exact @GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero | exact GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero | (intros; apply GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.SpinRel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def quadM (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b

theorem term_comm {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g e : Fin n) :
    c a e * c e b * c d g - c d g * (c a e * c e b) =
      (if b = d then (if e = g then (2 : ℂ) • c a g else 0) else 0) -
        (if a = g then (if e = d then (2 : ℂ) • c d b else 0) else 0) := by
  have h1 := hc.1 e b d g
  have h2 := hc.1 a e d g
  have h : c a e * c e b * c d g - c d g * (c a e * c e b) =
      c a e * (c e b * c d g + c d g * c e b) - (c a e * c d g + c d g * c a e) * c e b := by
    noncomm_ring
  rw [h, h1, h2]
  by_cases hbd : b = d <;> by_cases heg : e = g <;> by_cases hag : a = g <;> by_cases hed : e = d <;>
    simp only [hbd, heg, hag, hed, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_zero, zero_mul, sub_zero, two_smul, mul_two, two_mul] <;> simp_all [two_smul, mul_two, two_mul]

theorem quad_c {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g : Fin n) :
    quadM c a b * c d g - c d g * quadM c a b =
      (if b = d then c a g else 0) - (if a = g then c d b else 0) := by
  have h : quadM c a b * c d g - c d g * quadM c a b =
      (1 / 2 : ℂ) • ∑ e, (c a e * c e b * c d g - c d g * (c a e * c e b)) := by
    simp only [quadM, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm hc, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hag : a = g <;>
    simp [hbd, hag, smul_sub, smul_smul]

theorem quad_quad {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d e : Fin n) :
    quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (if b = d then quadM c a e else 0) - (if e = a then quadM c d b else 0) := by
  have h : ∀ f, quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b =
      ((if b = d then c a f else 0) - (if a = f then c d b else 0)) * c f e +
        c d f * ((if b = f then c a e else 0) - (if a = e then c f b else 0)) := by
    intro f
    rw [← quad_c hc a b d f, ← quad_c hc a b f e]
    noncomm_ring
  have h2 : quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (1 / 2 : ℂ) • ∑ f, (quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b) := by
    conv_lhs => rw [show quadM c d e = (1 / 2 : ℂ) • ∑ f, c d f * c f e from rfl]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h2]
  simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hae : a = e
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel

theorem spinM_eq (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    spinM c a b = quadM c a b - (if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0) := rfl

theorem spin_glRel {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) : Formalism.REAL.GlRel (spinM c) := by
  intro a b d e
  have h := quad_quad hc a b d e
  have hcomm : spinM c a b * spinM c d e - spinM c d e * spinM c a b =
      quadM c a b * quadM c d e - quadM c d e * quadM c a b := by
    simp only [spinM_eq]
    by_cases hab : a = b <;> by_cases hde : d = e <;>
      simp only [hab, hde, if_true, if_false, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one] <;> module
  rw [hcomm, h]
  by_cases hbd : b = d
  · by_cases hea : e = a
    · subst hbd
      subst hea
      simp [spinM_eq]
    · have hae : ¬ a = e := fun h => hea h.symm
      subst hbd
      simp [spinM_eq, hea, hae]
  · by_cases hea : e = a
    · have hdb : ¬ d = b := fun h => hbd h.symm
      simp [spinM_eq, hbd, hea, hdb]
    · simp [hbd, hea]

theorem spin_conjTranspose {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b : Fin n) :
    (spinM c a b)ᴴ = spinM c b a := by
  simp only [spinM_eq, quadM]
  by_cases hab : a = b
  · subst hab
    simp [conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul, Complex.conj_ofNat]
  · simp [hab, Ne.symm hab, conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul]

theorem spinRel : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a :=
  fun _ hc => ⟨spin_glRel hc, spin_conjTranspose hc⟩

end GlobalTheory.CompanionTheory.RealCount.SpinRel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqIntAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  have := hc.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this

end GlobalTheory.CompanionTheory.SqIntFD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantContractsUnipotentStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictly_dominant_contracts_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  first | exact @GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | exact GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN | (intros; apply GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEq
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepSecondIso

theorem subQuot_equiv_of_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A →
    Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  intro G V _ _ _ ρ A B E hEA hsup
  have hEA' : E.toSubmodule ≤ A.toSubmodule := fun x hx => hEA hx
  let PE := Submodule.comap E.toSubmodule.subtype B.toSubmodule
  let PA := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA := PA.mkQ ∘ₗ Submodule.inclusion hEA'
  have hf : PE ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  let φ := PE.liftQ f hf
  have hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective PE q
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective PA q
    have ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, hsup]
      exact a.2
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp ha
    refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
    rw [hφ, Submodule.Quotient.eq]
    show e - (a : V) ∈ B.toSubmodule
    have hdiff : e - (a : V) = -b := by
      rw [← hab]
      abel
    rw [hdiff]
    exact B.toSubmodule.neg_mem hb
  let ψ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x)
    (fun y => ψ.apply_symm_apply y)⟩
  exact Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)

end GlobalTheory.CompanionTheory.RepSecondIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubreps
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SubquotPres

theorem exists_equiv_subQuot : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W),
    IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  intro G V W _ _ _ _ _ ρ π h
  obtain ⟨S, f, hf⟩ := h
  have hint : ∀ (g : G) (x : S.toSubmodule),
      f.toLinearMap (S.toRepresentation g x) = π g (f.toLinearMap x) := fun g x => by
    simpa only [Representation.IntertwiningMap.toLinearMap_apply] using
      Representation.IntertwiningMap.isIntertwining _ _ f g x
  let K : Submodule ℂ S.toSubmodule := LinearMap.ker f.toLinearMap
  let B : Subrepresentation ρ := ⟨K.map S.toSubmodule.subtype, by
    intro g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨S.toRepresentation g x, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hint, hx, map_zero]⟩
  have hBS : B ≤ S := by
    show K.map S.toSubmodule.subtype ≤ S.toSubmodule
    exact Submodule.map_subtype_le _ _
  have hQ : Submodule.comap S.toSubmodule.subtype B.toSubmodule = K :=
    Submodule.comap_map_eq_of_injective Subtype.val_injective K
  let φ := Submodule.liftQ (Submodule.comap S.toSubmodule.subtype B.toSubmodule) f.toLinearMap hQ.le
  have hφ : ∀ x : S.toSubmodule, φ (Submodule.Quotient.mk x) = f.toLinearMap x := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hQ.ge
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk x, by rw [hφ, Representation.IntertwiningMap.toLinearMap_apply]⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hφint : ∀ (g : G) q, φ (GlobalTheory.SmGL.subQuot S B g q) = π g (φ q) := by
    intro g q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact hint g x
  have hT : ∀ g : G, e.symm.toLinearMap ∘ₗ π g =
      GlobalTheory.SmGL.subQuot S B g ∘ₗ e.symm.toLinearMap := by
    intro g
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    obtain ⟨q, rfl⟩ := e.surjective w
    rw [LinearEquiv.symm_apply_apply]
    exact (hφint g q).symm
  let T : Representation.IntertwiningMap π (GlobalTheory.SmGL.subQuot S B) :=
    ⟨e.symm.toLinearMap, hT⟩
  exact ⟨S, B, hBS, ⟨Representation.Equiv.mk' T e (fun w => e.apply_symm_apply w)
    (fun q => e.symm_apply_apply q)⟩⟩

end GlobalTheory.CompanionTheory.SubquotPres
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumTwOrbitEqZero
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.FiniteFourier

open GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_twOrbit_eq_zero {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (L₁ : Subgroup L) (hL₁ : IsOpen (L₁ : Set L)) (v : V)
    (hv : ∀ x ∈ L₁, ρ (x : G) v = v) (θ : L →* ℂˣ) (hθ : ∀ x ∈ L₁, θ x = 1)
    (hk : v ∈ twKer ρ L θ) [L₁.Normal] [Fintype (L ⧸ L₁)] :
    ∑ q : L ⧸ L₁, twOrbit ρ L θ v q.out = 0 := by
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hle : L₁ ≤ θ.ker := fun x hx => hθ x hx
  have hopen : IsOpen (θ.ker : Set L) := Subgroup.isOpen_mono hle hL₁
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hopen hk
  haveI : L₁.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set C : Subgroup L := (M ⊓ L₁).normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal _
  haveI : C.FiniteIndex := inferInstance
  haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ L₁ := Subgroup.normalCore_le _
  haveI : Finite (L₁ ⧸ C.subgroupOf L₁) := inferInstance
  haveI : Fintype (L₁ ⧸ C.subgroupOf L₁) := Fintype.ofFinite _
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
    (fun x k hk => twOrbit_mul_right ρ L θ v x k ⟨hv k hk, hθ k hk⟩)] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem eq_zero_of_twKer :
    ∀ {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ (L₁ : Subgroup L), IsOpen (L₁ : Set L) → ∀ (v : V), (∀ x ∈ L₁, ρ (x : G) v = v) → ∀ {ι : Type} (R : Finset ι), R.Nonempty → ∀ (χ : ι → (L →* ℂˣ)), (∀ a ∈ R, ∀ x ∈ L₁, χ a x = 1) → (∀ a ∈ R, v ∈ twKer ρ L (χ a)) → (∀ x : L, x ∉ L₁ → ∑ a ∈ R, (((χ a x)⁻¹ : ℂˣ) : ℂ) = 0) → v = 0 := by
  intro G V _ _ _ _ _ ρ hρ L hL L₁ hL₁ v hv ι R hR χ hχ hker hsum
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ L₁) := Subgroup.quotient_finite_of_isOpen _ hL₁
  haveI : L₁.Normal := Subgroup.normal_of_comm L₁
  haveI : Fintype (L ⧸ L₁) := Fintype.ofFinite _
  have key : ∀ a ∈ R, ∑ q : L ⧸ L₁, twOrbit ρ L (χ a) v q.out = 0 := fun a ha =>
    sum_twOrbit_eq_zero ρ hρ L hL L₁ hL₁ v hv (χ a) (hχ a ha) (hker a ha)
  have h0 : ∑ q : L ⧸ L₁, ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero key
  have hoff : ∀ q : L ⧸ L₁, q ≠ 1 → ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    intro q hq
    have hnot : q.out ∉ L₁ := by
      intro hmem
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    simp only [twOrbit]
    rw [← Finset.sum_smul, hsum _ hnot, zero_smul]
  have hone : ((1 : L ⧸ L₁).out : L) ∈ L₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hmain : ∑ a ∈ R, twOrbit ρ L (χ a) v (1 : L ⧸ L₁).out = R.card • v := by
    rw [Finset.card_eq_sum_ones, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [twOrbit]
    rw [hχ a ha _ hone, hv _ hone]
    simp
  rw [Finset.sum_eq_single (1 : L ⧸ L₁) (fun q _ hq => hoff q hq)
    (fun h => absurd (Finset.mem_univ _) h), hmain] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 hR.card_pos.ne')
  · exact h0

end GlobalTheory.CompanionTheory.FiniteFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

theorem sup_eq_of_isIrreducible_subQuot :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B →
      E ⊔ B = A := by
  intro G V _ _ _ ρ A B E hBA hirr hEA hEB
  haveI : IsSimpleOrder (Subrepresentation (GlobalTheory.SmGL.subQuot A B)) := hirr
  refine le_antisymm (sup_le hEA hBA) ?_
  let P := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let S : Submodule ℂ (A.toSubmodule ⧸ P) :=
    Submodule.map P.mkQ (Submodule.comap A.toSubmodule.subtype (E ⊔ B).toSubmodule)
  have hS : ∀ (g : G) ⦃q : A.toSubmodule ⧸ P⦄, q ∈ S →
      GlobalTheory.SmGL.subQuot A B g q ∈ S := by
    intro g q hq
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨⟨ρ g y, A.apply_mem_toSubmodule g y.2⟩, (E ⊔ B).apply_mem_toSubmodule g (v := (y : V)) hy, rfl⟩
  let W : Subrepresentation (GlobalTheory.SmGL.subQuot A B) := ⟨S, hS⟩
  obtain ⟨e, heE, heB⟩ := SetLike.not_le_iff_exists.mp hEB
  have hea : e ∈ A.toSubmodule := hEA heE
  have heEB : e ∈ (E ⊔ B).toSubmodule := (le_sup_left : E ≤ E ⊔ B) heE
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · exfalso
    let Z : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊥, fun g q hq => by
        rw [Submodule.mem_bot] at hq ⊢
        rw [hq, map_zero]⟩
    have hmem : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ W := by
      show _ ∈ S
      exact Submodule.mem_map.mpr ⟨⟨e, hea⟩, heEB, rfl⟩
    rw [hW] at hmem
    have hZ : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ Z := (bot_le : ⊥ ≤ Z) hmem
    have hZ' : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ (⊥ : Submodule ℂ (A.toSubmodule ⧸ P)) := hZ
    have h0 : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ = 0 := (Submodule.mem_bot ℂ).mp hZ'
    have heP : (⟨e, hea⟩ : A.toSubmodule) ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact heB heP
  · intro x hx
    have hxA : x ∈ A.toSubmodule := hx
    let T : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
    have hT : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ W := by
      rw [hW]
      exact (le_top : T ≤ ⊤)
        (show Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ (⊤ : Submodule ℂ (A.toSubmodule ⧸ P)) from
          Submodule.mem_top)
    have hT' : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ S := hT
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hT'
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hyx
    have hb : (y : V) - x ∈ B.toSubmodule := hyx
    have hb' : (y : V) - x ∈ (E ⊔ B).toSubmodule := (le_sup_right : B ≤ E ⊔ B) hb
    have hy' : (y : V) ∈ (E ⊔ B).toSubmodule := hy
    have hsub := (E ⊔ B).toSubmodule.sub_mem hy' hb'
    rw [sub_sub_cancel] at hsub
    exact hsub

end GlobalTheory.CompanionTheory.GenCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

theorem rank_piTensorProduct_le_one {α : Type} [Fintype α] (M : α → Type)
    [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (h : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)
  rw [rank_le_one_iff]
  refine ⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    choose c hc using fun a => hv₀ a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • v₀ a := funext fun a => (hc a).symm
    rw [hf, MultilinearMap.map_smul_univ, mul_smul]
  · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [add_smul, hr, hs]⟩

end GlobalTheory.CompanionTheory.TensorRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)
end

