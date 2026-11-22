import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbit
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealOrbitMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_homeomorph (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃ₜ (I → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

theorem mat_inv_mul {P Q : ℕ} (t : UpqT P Q) : UpqT.mat t⁻¹ * UpqT.mat t = 1 :=
  Units.inv_mul (show Formalism.UG.Upq P Q from t).1

theorem theta_projInf {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    (fun i => θ (projInf (h • ratTup (F := F) (AF F) x) 0 i)) = infMat σ J θ h *ᵥ fun i => τ (x 0 i) := by
  funext i
  let p : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e := RingHom.map_mulVec (θ.comp p) (HA.mat (AF F) σ J h).1 (ratTup (F := F) (AF F) x 0) i
  refine e.trans ?_
  have e2 : (θ.comp p) ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := by
    funext j
    rw [← hθ.1]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 ⊗ₜ x 0 j)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [e2]
  rfl

theorem realOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  intro F E _ _ _ _ _ σ hcm I _ τ hτ θ hθ M P Q J A N hl hr x
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph hcm hτ hθ
  let v : (I → UpqT P Q) → I → Fin P ⊕ Fin Q → ℂ := fun g ρ => UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))
  have key : ∀ (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : I → Fin P ⊕ Fin Q → ℂ),
      (∀ ρ, infCoord (θ ρ) (A ρ) Y = w ρ) ↔ Y = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ w ρ) i := by
    intro Y w
    constructor
    · intro hY
      funext a i
      obtain rfl : a = 0 := Subsingleton.elim _ _
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      funext ρ
      rw [hΦ, ← hY ρ, infCoord, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · rintro rfl ρ
      have : (fun i => θ ρ (Φ.symm fun ρ => (N ρ *ᵥ w ρ) i)) = N ρ *ᵥ w ρ := by
        funext i
        rw [← hΦ, Φ.apply_symm_apply]
      rw [infCoord, this, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  refine ⟨⟨fun g _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i, fun g => (key _ (v g)).2 rfl⟩, fun pt hpt => ?_⟩
  have hpt' : ∀ g, pt g = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i := fun g => (key _ (v g)).1 (hpt g)
  refine ⟨?_, fun g g' hg => ?_, fun h t ht => ?_⟩
  · haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
    haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
    haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (UpqT P Q) :=
      (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
    rw [show pt = _ from funext hpt']
    refine measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun i => Continuous.measurable ?_
    refine Φ.symm.continuous.comp (continuous_pi fun ρ => (continuous_apply i).comp (f := fun a => N ρ *ᵥ v a ρ) ?_)
    exact continuous_const.matrix_mulVec
      ((GlobalTheory.VolPairExists.continuous_mat.comp (continuous_apply ρ).inv).matrix_mulVec continuous_const)
  · rw [hpt', hpt', show v g = v g' from funext hg]
  · rw [hpt']
    refine ((key _ (v t)).1 fun ρ => ?_).symm
    have e : A ρ * infMat σ J (θ ρ) h⁻¹ = UpqT.mat (t ρ)⁻¹ * A ρ := by
      calc A ρ * infMat σ J (θ ρ) h⁻¹
          = UpqT.mat (t ρ)⁻¹ * (UpqT.mat (t ρ) * A ρ) * infMat σ J (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
        _ = UpqT.mat (t ρ)⁻¹ * A ρ := by
            rw [ht, Matrix.mul_assoc, Matrix.mul_assoc, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, mul_inv_cancel,
              Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_one, Matrix.mul_one]
    rw [infCoord, theta_projInf (hθ ρ), Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]

end GlobalTheory.RealOrbitMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevel
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.AdelicOrbit

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem parts_inj (x y : AF F ⊗[F] E)
    (h1 : (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom y)
    (h2 : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem mem_parts (g : GL (Fin M) (AF F ⊗[F] E)) :
    g ∈ HR (AF F) σ J ↔
      Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g ∈ HR (Af F) σ J := by
  have := GlobalTheory.UnitarySplit.mem_iff _ _ (parts_inj (F := F) (E := E)) (sigR _ σ) (sigR _ σ) (sigR _ σ)
    (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g
  rw [GlobalTheory.UnitarySplit.map_JR, GlobalTheory.UnitarySplit.map_JR] at this
  exact this

theorem exists_fin (h : HA (AF F) σ J) :
    ∃ k : HA (Af F) σ J, (HA.mat (Af F) σ J k).1 = finMat σ J h :=
  ⟨(⟨_, ((mem_parts σ J (HA.mat (AF F) σ J h)).1 h.2).2⟩ : HR (Af F) σ J), rfl⟩

theorem exists_lift (k : HA (Af F) σ J) :
    ∃ h : HA (AF F) σ J, finMat σ J h = (HA.mat (Af F) σ J k).1 ∧
      (HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hs : ∀ a b, ∃ x, (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x = a ∧
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue _ _ parts_inj hs 1 (HA.mat (Af F) σ J k)
  have hg : g ∈ HR (AF F) σ J := (mem_parts σ J g).2 ⟨g1 ▸ one_mem _, g2 ▸ k.2⟩
  exact ⟨(⟨g, hg⟩ : HR (AF F) σ J), congrArg Units.val g2, congrArg Units.val g1⟩

omit [NumberField E] in
theorem projFin_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    projFin (h • ratTup (F := F) (AF F) x) 0 = finMat σ J h *ᵥ fun i => inclR (F := F) (Af F) (x 0 i) := by
  funext i
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

omit [NumberField E] in
theorem projInf_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) (i : Fin M) :
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom ((h • ratTup (F := F) (AF F) x) 0 i) =
      ((HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom *ᵥ
        fun i => inclR (F := F) (Ainf F) (x 0 i)) i := by
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

end SlopeTestRemainingChoices

theorem mem_latHat_iff : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  intro hT F E _ _ _ _ _ σ hcm hur M J hJ L hL β hβ x hx hq h
  constructor
  · intro hm
    have hO := (hT F E σ hcm hur M J hJ L hL β hβ (x 0) hx hq).2.1
    obtain ⟨k', hk'⟩ := exists_fin σ J h⁻¹
    have h1 : k'⁻¹ ∈ {h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x 0 i)) ∈
        latHat F E (L : Set (Fin M → E))} := by
      rw [Set.mem_setOf_eq, inv_inv, actV_eq, hk', ← projFin_smul]
      exact hm
    rw [hO] at h1
    obtain ⟨af, haf, kf, hkf, e⟩ := h1
    obtain ⟨a, ha1, ha2⟩ := exists_lift σ J af
    refine ⟨a, ?_, ?_⟩
    · change a • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x
      funext c i
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine parts_inj _ _ ?_ ?_
      · rw [projInf_smul, ha2, Matrix.one_mulVec]
        rfl
      · have h2 := congrFun (projFin_smul σ J a x) i
        rw [ha1] at h2
        refine h2.trans ?_
        have h3 : af • ratTup (F := F) (Af F) (fun _ : Fin 1 => x 0) = ratTup (F := F) (Af F) (fun _ => x 0) := haf
        exact congrFun (congrFun h3 0) i
    · have e' : k' * af = kf⁻¹ := by
        have e2 : af * kf = k'⁻¹ := e
        rw [← inv_inv k', ← e2]
        group
      have h2 : h⁻¹ * a ∈ stab σ J (L : Set (Fin M → E)) := by
        intro y
        rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ha1, ← hk', ← Matrix.mulVec_mulVec, ← actV_eq, ← actV_eq, ← actV_mul, e']
        exact (inv_mem hkf : kf⁻¹ ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E)))) y
      have h3 := inv_mem h2
      rwa [_root_.mul_inv_rev, inv_inv] at h3
  · rintro ⟨a, ha, hk⟩
    have h1 : a⁻¹ • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x := inv_mem ha
    have h2 : h⁻¹ • ratTup (F := F) (AF F) x = (a⁻¹ * h)⁻¹ • ratTup (F := F) (AF F) x := by
      conv_rhs => rw [← h1, ← mul_smul]
      congr 1
      group
    rw [h2, projFin_smul]
    exact ((inv_mem hk : (a⁻¹ * h)⁻¹ ∈ stab σ J (L : Set (Fin M → E))) _).1
      (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x 0, hx, rfl⟩)

end GlobalTheory.AdelicOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabEmbClosed

theorem isClosedEmbedding_conj_fromBlocks {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m (n ⊕ Unit) ℂ) (N : Matrix (n ⊕ Unit) m ℂ) (hNM : N * M = 1) :
    IsClosedEmbedding
      (fun X : Matrix n n ℂ => M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun Y : Matrix m m ℂ => (N * Y * M).toBlocks₁₁) ?_ ?_ ?_
  · intro X
    have : N * (M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) * M
        = fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) := by
      calc _ = (N * M) * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * (N * M) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hNM, Matrix.one_mul, Matrix.mul_one]
    simp only [this, toBlocks_fromBlocks₁₁]
  · have h : Continuous fun Y : Matrix m m ℂ => N * Y * M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.matrix_submatrix Sum.inl Sum.inl
  · exact (continuous_const.matrix_mul
      (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const

theorem isClosedEmbedding_of_isStabEmb : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  intro P Q P' Q' hd x₀ hx j hj
  obtain ⟨C, hC, hCx, hj⟩ := hj
  obtain ⟨N, B, hNM, hMN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hd hx hC hCx
  have key : ∀ g : UpqT P' Q', (j g).mat =
      C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) * N := by
    intro g
    obtain ⟨h1, h2⟩ := hj g
    have h3 : (j g).mat * replicateCol Unit x₀ = replicateCol Unit x₀ := by
      rw [← replicateCol_mulVec, h1]
    have h4 : (j g).mat * C.fromCols (replicateCol Unit x₀) =
        C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) := by
      rw [mul_fromCols, fromCols_mul_fromBlocks, h2, h3]
      simp
    rw [← h4, Matrix.mul_assoc, hMN, Matrix.mul_one]
  refine IsClosedEmbedding.of_comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)).isEmbedding ?_
  have := (isClosedEmbedding_conj_fromBlocks _ N hNM).comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P') (Q := Q'))
  convert this using 1
  funext g
  exact key g

end GlobalTheory.StabEmbClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
section
noncomputable section

namespace GlobalTheory.LvT.Built.TopEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
  {u : Pr.Word} {A : Amb X}

theorem kerOf_xiTop (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) {T : ChTh W sel mu u m2} (hT : ChTh.Ok (Ch := Ch) cst T)
    (al : L.β (m2 + 1)) (c : TopStep.TopDepth R cst.M) (g : FrmG (L.levG (m2 + 1) al) (L.levQ (m2 + 1) al))
    (g' : FrmG (TopStep.topLevG Ch (rPsymF (R := R) Ch)) (TopStep.topLevQ R sel mu c.pos)) (p : ChPt (R := R) sel mu u (m2 + 1))
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (p' : ChPt (R := R) sel mu u R.m) :
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (g • p).deco.1.N (frsF sel mu (g • p)) (g' • p').deco.1.N
        (frsF sel mu (g' • p')) (TopStep.XiTop Ch sel mu cst m2 (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) =
      frmRho (colValF W sel mu u R.m) _ _ g' ∘ₗ
        kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p')
          (TopStep.XiTop Ch sel mu cst m2 p Y p') ∘ₗ frmRho (colValF W sel mu u (m2 + 1)) _ _ g⁻¹ := by
  have hY' : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N := (ybSet_gmap sel mu cst _ g.1.1 Y).2 hY
  have hd := (TopStep.tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  obtain ⟨κ, a, hκ, ha, ea⟩ := TopLaw.exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := TopLaw.exists_pass hd g' p'
  have key := GlobalTheory.kerOf_gmap_frames T.top (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _
    hT.top g.1 g'.1 p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (TopStep.XiTop Ch sel mu cst m2 p Y p')
    (TopStep.XiTop Ch sel mu cst m2 (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (GlobalTheory.TopXiInv.xiTop_invariant Ch sel mu cst m2 u hPr hL.hm hL.cst_ok hL.depthQ p Y p' hY) fun x =>
      TopLaw.xiTop_law c hX hPr hsel hL (Or.inr ⟨hs, rfl⟩) hY hY' hκ hκ' ha ha' x (TopLaw.phiT_act _ _ _ _ _ _ _)
  rw [funext hκ, funext hκ']
  refine key.trans ?_
  have ei : (∏ P, a P)⁻¹ = (L.levG (m2 + 1) al).chr g.2.1⁻¹ * (L.levQ (m2 + 1) al).chr g.2.2⁻¹ := by
    rw [ea, mul_inv, map_inv, map_inv]
  exact (congrArg (fun z : X.Kˣ => (z : X.K) • _) (congrArg₂ (· * ·) ea' ei)).trans (TopLaw.smul_comp_smul _ _ _ _ _)

theorem ker_xiOver (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) (hT : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    {j : ℕ} (h : j = R.m) (al : L.β (m2 + 1)) {Λ : LevFam X.E X.K (R.N j) Pr.vGs}
    {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (hΛ : Λ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levG j) (hΘ : Θ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levQ j)
    (g : FrmG (L.levG (m2 + 1) al) (L.levQ (m2 + 1) al)) (g' : FrmG Λ Θ) (p : ChPt (R := R) sel mu u (m2 + 1))
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (p' : ChPt (R := R) sel mu u j) :
    GlobalTheory.KerT.ker W Ch sel mu cst A u (m2 + 1) j (g • p).deco.1.N (frsF sel mu (g • p)) (g' • p').deco.1.N (frsF sel mu (g' • p'))
                 (xiOver Ch sel mu cst m2 h (g • p) ((fun v => g.1.1 v) '' Y) (g' • p')) =
      frmRho (colValF W sel mu u j) _ _ g' ∘ₗ
        GlobalTheory.KerT.ker W Ch sel mu cst A u (m2 + 1) j p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p')
          (xiOver Ch sel mu cst m2 h p Y p') ∘ₗ frmRho (colValF W sel mu u (m2 + 1)) _ _ g⁻¹ := by
  subst h
  obtain rfl := hΛ.trans (topLev_levG_m_eq Ch sel mu cst _)
  obtain rfl := hΘ.trans (topLev_levQ_m_eq Ch sel mu cst _)
  have e3 : (chTh W Ch sel mu cst A u m2).top = stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m) :=
    stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u (m2 + 1) (by have := hL.hm; omega) (W.lamTrue u R.m)
  have key := kerOf_xiTop hX hPr hsel hS hL hs hT al default g g' p hY p'
  rw [e3] at key
  exact key

theorem kAt_top_equiv (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X) (hX : X.Ok) (hPr : Pr.Ok) (_hCh : Ch.Ok) (hsel : IsSel X sel)
    (hTS : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S) (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true)
    (hT : ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2)) (hi : i + 1 = R.m) b b'
    (g : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).G b)
    (g' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).G b')
    (d : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).D b)
    (d' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).D b') :
    kAt W Ch sel mu cst L A u i b b'
        (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).actD b; g • d)
        (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).actD b'; g' • d') =
      (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ
        kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ
          (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).rho X.emb (W.lamTrue u i) b g⁻¹ := by
  obtain rfl : i = m2 + 1 := by have := hL.hm; omega
  have hY := PtAt.mem_ybSet d hi
  unfold kAt
  rw [xiAt_last Ch sel mu cst L hi, xiAt_last Ch sel mu cst L hi]
  obtain ⟨_ | al, hb⟩ := b
  · exact absurd (hb.2 (by omega)) (by simp)
  exact ker_xiOver hX hPr hsel ⟨hTS, hg⟩ hL hs hT hi al (levGAt_of_le sel mu L _ hi.ge b') (levQAt_of_le sel mu L _ hi.ge b')
    g g' d.1.1 hY d'.1.1

end GlobalTheory.LvT.Built.TopEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlacStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  first | exact @GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | exact GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion | (intros; apply GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDual
section
noncomputable section

namespace GlobalTheory.VolStabImage

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem map_restrict_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  intro F E _ _ _ _ _ σ hcm I _ τ θ hθ M P Q hM J hJ A hA L hL cd μ hμ
  have hd : ∀ ρ, IsUnit (J.map (τ ρ)).det := fun ρ => by
    have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    rw [this]
    exact ((map_ne_zero (τ ρ)).2 hJ).isUnit
  let N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hl : ∀ ρ, N ρ * A ρ = 1 := fun ρ => by
    change (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q) * A ρ = 1
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (hd ρ)]
  have e : Fin M ≃ (Fin P ⊕ Fin Q) := Fintype.equivOfCardEq (by simpa using hM)
  have hr : ∀ ρ, A ρ * N ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv e).1 (hl ρ)
  refine ⟨⟨N, hl, hr⟩, ?_⟩
  choose ψ hψ hψm using fun ρ => GlobalTheory.VolPairExists.exists_hom _ (continuous_infMat J (hθ ρ))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul σ J (θ ρ)) (infMat_unitary J hcm (hθ ρ)) (hA ρ) (hl ρ) (hr ρ)
  have hψA : ∀ h ρ, UpqT.mat (ψ ρ h) * A ρ = A ρ * infMat σ J (θ ρ) h := fun h ρ => by
    rw [hψm, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hc : Continuous (MonoidHom.pi ψ) := continuous_pi hψ
  refine ⟨MonoidHom.pi ψ, hc, hψA, ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := cd.haar P Q
  refine (Measure.pi_eq fun B hB => ?_).symm
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Measure.map_apply hc.measurable hm, Measure.restrict_apply (hc.measurable hm), ← hμ B hB]
  congr 1
  ext h
  refine and_comm.trans (and_congr Iff.rfl ?_)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  refine forall_congr' fun ρ => ⟨fun hb => ⟨_, hb, hψA h ρ⟩, ?_⟩
  rintro ⟨b, hb, hbA⟩
  have : b = ψ ρ h := GlobalTheory.VolPairExists.mat_injective (by
    rw [hψm, ← hbA, Matrix.mul_assoc, hr, Matrix.mul_one])
  subst this
  exact hb

end GlobalTheory.VolStabImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrime
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem norm_kappa_sq_mul_norm_det : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι u hu h1 h2 h3
  obtain ⟨γ, hγ, hdet⟩ := GlobalTheory.T.unitary_standard_at_q_from_isometry_over_field D cc δ B hcc hδ q hq2 hsplit hcop ι u hu h1 h2 h3
  rw [hdet]
  exact GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one D B.γ₀ γ B.kc q hq2 hsplit hγ ι

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsTheta
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
end

