import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0137
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDualStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  first | exact @GlobalTheory.VolStabImage.map_restrict_stab | exact GlobalTheory.VolStabImage.map_restrict_stab | (intros; apply GlobalTheory.VolStabImage.map_restrict_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrimeStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | exact GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | (intros; apply GlobalTheory.MomN.norm_kappa_sq_mul_norm_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsThetaStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedThetaVector_isometry_isTheta : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  first | exact @GlobalTheory.IsomTheta.isTheta_eNat_comp | exact GlobalTheory.IsomTheta.isTheta_eNat_comp | (intros; apply GlobalTheory.IsomTheta.isTheta_eNat_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodularStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbitStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_vectors_same_length_one_unitary_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.RatOrbit.rational_sphere_orbit | exact GlobalTheory.RatOrbit.rational_sphere_orbit | (intros; apply GlobalTheory.RatOrbit.rational_sphere_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexConjLevelVL
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.StabConjIndex

theorem relIndex_conj_comm {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) (K : Subgroup H) (ho : IsOpen (K : Set H))
    (hc : IsCompact (K : Set H)) (g : H) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have e : (K' : Set H) = (fun x => g⁻¹ * x) ⁻¹' ((fun x => x * g) ⁻¹' (K : Set H)) := by
    ext x
    simp only [hK', SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  have ho' : IsOpen (K' : Set H) := by
    rw [e]
    exact (ho.preimage (continuous_mul_const g)).preimage (continuous_const_mul g⁻¹)
  have hc' : IsCompact (K' : Set H) := by
    rw [hK', Subgroup.coe_map]
    exact hc.image (f := fun x => g * x * g⁻¹) (by fun_prop)
  have hμ : μ K' = μ K := by rw [e, measure_preimage_mul, measure_preimage_mul_right]
  have hoi : IsOpen ((K ⊓ K' : Subgroup H) : Set H) := ho.inter ho'
  have key : ∀ L : Subgroup H, IsCompact (L : Set H) → K ⊓ K' ≤ L →
      ((K ⊓ K').relIndex L : ENNReal) * μ (K ⊓ K' : Subgroup H) = μ L := fun L hL hle => by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
    haveI : Finite (L ⧸ (K ⊓ K').subgroupOf L) :=
      Subgroup.quotient_finite_of_isOpen _ (hoi.preimage continuous_subtype_val)
    haveI : ((K ⊓ K').subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact GlobalTheory.BaseModule.relIndex_mul_measure' _ _ hle hoi.measurableSet μ
  have h1 := key K hc inf_le_left
  have h2 := key K' hc' inf_le_right
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right, hμ, ← h1] at h2
  have h0 : μ (K ⊓ K' : Subgroup H) ≠ 0 := (hoi.measure_pos μ ⟨1, one_mem _⟩).ne'
  have ht : μ (K ⊓ K' : Subgroup H) ≠ ⊤ :=
    ((measure_mono (show ((K ⊓ K' : Subgroup H) : Set H) ⊆ K from inf_le_left (a := K))).trans_lt
      hc.measure_lt_top).ne
  exact_mod_cast ((ENNReal.mul_left_inj h0 ht).1 h2).symm

section Transport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

noncomputable def swap : (v.adicCompletion F ⊗[F] E) ≃+* (E ⊗[F] v.adicCompletion F) :=
  (Algebra.TensorProduct.comm F _ _).toRingEquiv

omit [NumberField E] in
theorem swap_tmul (a : v.adicCompletion F) (x : E) : swap v (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := rfl

theorem swap_mem_int (y : v.adicCompletion F ⊗[F] E) : y ∈ GlobalTheory.AdelicU.intLoc F E v ↔
    swap v y ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  constructor
  · refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => swap v y ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) (fun a ha x => ?_)
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy)
    have : swap v (a ⊗ₜ[F] (x : E)) = ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
      rw [swap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · intro h
    have : tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (swap (E := E) v).symm.toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) x
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc ha 1
    simpa using this h

theorem swap_mem_lat (N : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → v.adicCompletion F ⊗[F] E) :
    y ∈ GlobalTheory.AdelicU.latLoc F N v ↔ (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N := by
  constructor
  · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
      (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_)
    · have h := Submodule.smul_mem (latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
        ⟨(1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert h using 1
      funext i
      change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : v.adicCompletion F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · convert Submodule.zero_mem _ using 1
      funext i
      exact map_zero _
    · convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    · convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  · intro h
    have : ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N,
        (fun i => (swap v).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F N v := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact GlobalTheory.AdelicU.tmul_mem_latLoc (one_mem _) hx
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i
        exact map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        funext i
        exact map_add _ _ _
      | smul c y _ hy =>
        have := (GlobalTheory.AdelicU.latLoc F N v).smul_mem
          ⟨(swap v).symm c.1, (swap_mem_int v _).2 (by simpa using c.2)⟩ hy
        convert this using 1
        funext i
        exact map_mul (swap v).symm c.1 (y i)
    simpa using this _ h

omit [NumberField E] in
theorem mem_UPts_swap (g : GL (Fin n) (v.adicCompletion F ⊗[F] E)) :
    bc (swap (E := E) v).toRingHom g ∈ UPts σ J (v.adicCompletion F) ↔ g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (v.adicCompletion F) σ J := by
  have hs : ∀ x, sigR σ (v.adicCompletion F) (swap v x) = swap v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) =
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (swap (E := E) v).toRingHom := by
    ext i j
    exact hs _
  have h2 : J.map (inclE (F := F) (v.adicCompletion F)) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (v.adicCompletion F) J).map (swap (E := E) v).toRingHom := rfl
  change cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) * _ * g.1.map (swap (E := E) v).toRingHom = _ ↔
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1 * _ * g.1 = _
  rw [h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective (swap v).injective).eq_iff

noncomputable def toGL : GlobalTheory.AdelicU.GLoc σ J v →* GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
  (bc (swap (E := E) v).toRingHom).comp (GlobalTheory.AdelicU.matHom _ σ J)

omit [NumberField E] in
theorem toGL_injective : Function.Injective (toGL σ J v) := fun _ _ h =>
  GlobalTheory.AdelicU.matHom_injective _ σ J
    (Units.ext (Matrix.map_injective (swap v).injective (congrArg Units.val h)))

omit [NumberField E] in
theorem exists_toGL {γ : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : γ ∈ UPts σ J (v.adicCompletion F)) :
    ∃ g, toGL σ J v g = γ := by
  have e : bc (swap (E := E) v).toRingHom (bc (swap (E := E) v).symm.toRingHom γ) = γ := by
    ext i j
    exact (swap v).apply_symm_apply _
  exact ⟨⟨bc (swap (E := E) v).symm.toRingHom γ, (mem_UPts_swap σ J v _).1 (e.symm ▸ h)⟩, e⟩

theorem map_stabLoc (N : Submodule (𝓞 E) (Fin n → E)) :
    (GlobalTheory.AdelicU.stabLoc σ J N v).map (toGL σ J v) = levelVL σ J v N := by
  have key : ∀ g, g ∈ GlobalTheory.AdelicU.stabLoc σ J N v ↔ toGL σ J v g ∈ stabGL (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) := fun g => by
    have hm : ∀ y : Fin n → v.adicCompletion F ⊗[F] E,
        (fun i => swap v (((GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y) i)) =
          (toGL σ J v g).1 *ᵥ fun i => swap v (y i) := fun y =>
      funext fun i => RingHom.map_mulVec (swap (E := E) v).toRingHom _ y i
    rw [GlobalTheory.AdelicU.mem_stabLoc]
    simp only [swap_mem_lat, hm]
    refine ⟨fun h x => ?_, fun h y => h _⟩
    simpa using h fun i => (swap v).symm (x i)
  ext γ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_UPts_swap σ J v _).2 g.2, (key g).1 hg⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨g, rfl⟩ := exists_toGL σ J v h1
    exact ⟨g, (key g).2 h2, rfl⟩

end Transport

theorem relIndex_conj_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (hc.sig : E →+* E) J → IsUnit J.det → ∀ (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → Submodule.span E (N : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ γ ∈ UPts hc.sig J (v.adicCompletion F), ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom).relIndex (levelVL hc.sig J v N) = (levelVL hc.sig J v N).relIndex ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom) := by
  intro F E _ _ _ _ _ _ hc n J hJ hd N hN hspan v γ hγ
  obtain ⟨δ, hδ, hσδ⟩ : ∃ δ : E, δ ≠ 0 ∧ hc.sig δ = -δ := by
    by_contra! h
    have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (by
      by_contra hne
      exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
    have := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hs⟩).finrank_eq
    rw [hc.deg2, Module.finrank_self] at this
    omega
  haveI : Submodule.IsLattice E N := ⟨Module.Finite.iff_fg.1 hN, hspan⟩
  obtain ⟨g, rfl⟩ := exists_toGL hc.sig J v hγ
  have h := relIndex_conj_comm (GlobalTheory.HeckeDual.modular_eq_one hc.sig J (fun x => star_star x) hδ hσδ
    ⟨fun i j => congrFun (congrFun hJ i) j, hd.ne_zero⟩ v) _ (GlobalTheory.AdelicU.isOpen_stabLoc hc.sig J N v)
    (GlobalTheory.AdelicU.isCompact_stabLoc hc.sig J N v) g
  have e : ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (toGL hc.sig J v)).map
      (MulAut.conj (toGL hc.sig J v g)).toMonoidHom =
      ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (MulAut.conj g).toMonoidHom).map (toGL hc.sig J v) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext1 x
    simp
  rw [← map_stabLoc, e, Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _),
    Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _), h]

end GlobalTheory.StabConjIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLengthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateNormalizedVectorIntegralCombTensorPower
section
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.KerInert Formalism.L2.KerInert.ISd

theorem transl_normVec_int : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  intro D cc δ B hcc hδ χ hχ p _ lam N N' M M' hAdm hM hM' t ht
  obtain ⟨s, hs, hsM, hMs⟩ := hM
  obtain ⟨s', hs', hsM', hMs'⟩ := hM'
  have hp : p.Prime := Fact.out
  have spos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs))
  have spos' : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs'))
  set La0 := La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa0
  set La1 := La D (tor0 D cc δ) M (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa1
  set La2 := La D (tor0 D cc δ) M M' with hLa2
  have one_std : ∀ y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N', ((1 : ℕ) : D.host.E) • y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N' := by
    intro y hy; simpa using hy
  have one_M : ∀ y ∈ M, ((1 : ℕ) : D.host.E) • y ∈ M := by
    intro y hy; simpa using hy
  have k10 : ∀ z ∈ La1, (s * 1) • z ∈ La0 := fun z hz => La_smul cc δ s 1 hsM one_std hz
  have k21 : ∀ z ∈ La2, (1 * s') • z ∈ La1 := fun z hz => La_smul cc δ 1 s' one_M hMs' hz
  have k20 : ∀ z ∈ La2, (s * s') • z ∈ La0 := fun z hz => La_smul cc δ s s' hsM hMs' hz
  have k12 : ∀ z ∈ La1, (1 * s') • z ∈ La2 := fun z hz => La_smul cc δ 1 s' one_M hsM' hz
  have hδ0 : δ ≠ 0 := delta_nonzero_link D cc hcc δ hδ
  have hI : IO.HfInt (tor0 D cc δ) La2 := hermitian_form_integral_values D cc hcc δ hδ hδ0 N N' M M' hAdm

  let Q2 : VC D N N' → Prop := fun y => ∃ n : ℕ, 0 < n ∧ n • y ∈ La2
  have q2_add : ∀ x y, Q2 x → Q2 y → Q2 (x + y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : (n * m) • (x + y) = m • (n • x) + n • (m • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m n]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ hx m) (AddSubgroup.nsmul_mem _ hy n)
  have q2_2 : ∀ x ∈ La2, Q2 x := fun x hx => ⟨1, one_pos, by simpa using hx⟩
  have q2_1 : ∀ x ∈ La1, Q2 x := fun x hx => ⟨1 * s', by omega, k12 x hx⟩
  have cf_good : ∀ x y, Q2 x → Q2 y → Good lam (IO.cf (tor0 D cc δ) x y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    obtain ⟨q, hq⟩ := im_rat (tor0 D cc δ) hI hn hm hx hy
    exact good_cf lam _ x y q hq

  have R1 : Rep lam B.tor (fun y => y ∈ La1) (B.thHalf N N' M) (B.thZero N N') := by
    show Rep lam B.tor (fun y => y ∈ La1) (Iop D B.tor La0 La1 (B.thZero N N')) (B.thZero N N')
    refine rep_Iop (Pt := fun y => y = 0) (rep_self rfl) ?_ ?_
    · rintro x hx y rfl
      exact ⟨cf_good x 0 (q2_1 x hx) (q2_2 0 (zero_mem _)), by simpa using hx⟩
    · exact idx_coprime La0 La1 (s * 1) (by simpa using hs) k10

  have R2 : Rep lam B.tor (fun y => ∃ a ∈ La2, ∃ b ∈ La1, y = a + b) (B.thMoved N N' M M') (B.thZero N N') := by
    show Rep lam B.tor _ (Iop D B.tor La1 La2 (B.thHalf N N' M)) (B.thZero N N')
    refine rep_Iop R1 ?_ ?_
    · intro x hx y hy
      exact ⟨cf_good x y (q2_2 x hx) (q2_1 y hy), x, hx, y, hy, rfl⟩
    · exact idx_coprime La1 La2 (1 * s') (by simpa using hs') k21

  obtain ⟨n, hn, hnp, hnt⟩ := ht
  have R3 : Rep lam B.tor (TorsPrime D p La0) (U D B.tor t (B.thMoved N N' M M')) (B.thZero N N') := by
    refine rep_U t R2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    refine ⟨cf_good t _ ⟨n, hn, hnt⟩ (q2_add a b (q2_2 a ha) (q2_1 b hb)), ?_⟩
    refine ⟨n * (s * s'), Nat.mul_pos hn (Nat.mul_pos spos spos'), Nat.Coprime.mul hnp (Nat.Coprime.mul hs hs'), ?_⟩
    have e : (n * (s * s')) • (t + (a + b)) = (s * s') • (n • t) + (n • ((s * s') • a) + (n * s') • ((s * 1) • b)) := by
      simp only [smul_add, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_one, mul_assoc, mul_comm s' s]
    rw [e]
    exact add_mem (k20 _ hnt) (add_mem (AddSubgroup.nsmul_mem _ (k20 a ha) n)
      (AddSubgroup.nsmul_mem _ (k10 b hb) (n * s')))

  have hchi := RestC.chiFacUnit (D := D) χ hχ p lam N N' M M' hAdm ⟨s, hs, hsM, hMs⟩ ⟨s', hs', hsM', hMs'⟩
  have hgood : Good lam (Base.chiFac χ N N' M M') := ⟨hchi.1, le_of_eq hchi.2⟩
  have R4 := rep_smul hgood R3
  have e : U D B.tor t (B.eNat χ N N' M M') = fun z => Base.chiFac χ N N' M M' * U D B.tor t (B.thMoved N N' M M') z := by
    funext z
    exact IO.U_smul _ t _ _ z
  rw [e]
  obtain ⟨m, c, s₀, hc, hs₀, hF⟩ := R4
  exact ⟨m, c, s₀, hc, hs₀, hF⟩

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrimeStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  first | exact @GlobalTheory.MomN.weakApprox_split | exact GlobalTheory.MomN.weakApprox_split | (intros; apply GlobalTheory.MomN.weakApprox_split <;> assumption)
end

