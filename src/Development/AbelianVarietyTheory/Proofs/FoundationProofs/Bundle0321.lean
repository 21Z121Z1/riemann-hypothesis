import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_detRoot_cong_one_odd_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  first | exact @GlobalTheory.DetRootCong.char_root_eq_one | exact GlobalTheory.DetRootCong.char_root_eq_one | (intros; apply GlobalTheory.DetRootCong.char_root_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
section
noncomputable section

namespace GlobalTheory.DecompCompare

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G] (Γ K : Subgroup G)

end Group

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def stabEquiv (K : Subgroup (HA (AF F) σ J)) (g : HA (AF F) σ J) :
    stabAt σ J K g ≃ Unfold.stab (ratPts σ J) K g where
  toFun γ := ⟨⟨γ.1, ((mem_stabAt σ J K g γ.1).1 γ.2).1⟩, by
    have h := ((mem_stabAt σ J K g γ.1).1 γ.2).2
    rw [mul_assoc] at h
    exact h⟩
  invFun γ := ⟨γ.1.1, (mem_stabAt σ J K g γ.1.1).2 ⟨γ.1.2, by
    rw [mul_assoc]
    exact γ.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Stab

theorem frame_inv {n P Q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G P Q)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) :
    ∃ L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ, L * A = 1 ∧ A * L = 1 := by
  obtain ⟨A₀, L₀, h0, hl, hr⟩ := GlobalTheory.VolPairExists.exists_frame h
  obtain ⟨e, -⟩ := h
  have h1 : (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
    calc (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A
        = L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) := by simp only [Matrix.mul_assoc]
      _ = L₀ * Formalism.UG.Jpq P Q * (A₀ * L₀)ᴴ * Formalism.UG.Jpq P Q * A₀ := by
          rw [hA, ← h0, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = L₀ * (Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q) * A₀ := by
          rw [hr, Matrix.conjTranspose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [GlobalTheory.VolPairExists.jpq_mul_self, Matrix.mul_one, hl]
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv e).1 h1⟩

variable (D : D7)

theorem KSub_eq (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) :
    KSub D W P Q θ A = levelW D.sp.cm W := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun ρ => ?_⟩⟩
  have hsig : Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := by
    have := hW (embOf D ρ)
    rwa [hs] at this
  obtain ⟨L, hl, hr⟩ := frame_inv hsig (hA ρ)
  have hu : (infMat D.sp.cm.sig W.gram (θ ρ) h)ᴴ * W.gram.map (embOf D ρ) * infMat D.sp.cm.sig W.gram (θ ρ) h =
      W.gram.map (embOf D ρ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH (D := D) (θ := θ) hθ W h ρ
  refine ⟨GlobalTheory.VolPairExists.mkU _ (GlobalTheory.VolPairExists.conj_unitary (hA ρ) hr hu), Set.mem_univ _, ?_⟩
  rw [GlobalTheory.VolPairExists.mat_mkU, Matrix.mul_assoc, hl, Matrix.mul_one]

theorem exists_data (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q)) :
    (∃ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ) := by
  refine ⟨GlobalTheory.DualPairCompare.exists_infFam D, ?_⟩
  have hsig : ∀ ρ, Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := fun ρ => by
    have := hW (embOf D ρ)
    rwa [hs] at this
  choose A L hA _ using fun ρ => GlobalTheory.VolPairExists.exists_frame (hsig ρ)
  exact ⟨A, hA⟩

theorem isOpen_levelW (W : HSpace D.host.E) :
    IsOpen (levelW D.sp.cm W : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) :=
  GlobalTheory.StabOpen.isOpen_stab_latHat D W

end GlobalTheory.DecompCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory NumberField Matrix Topology GlobalTheory.Mem.Vol
open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.VolPairExists
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem infEmb_tmul (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (a : Ainf F) (x : E) : θ (a ⊗ₜ x) = GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) a * τ x :=
  haveI := h.1
  GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 a x

theorem infEmb_unique (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ θ' : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (hθ' : IsInfEmb τ θ') : θ = θ' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [infEmb_tmul h hθ, infEmb_tmul h hθ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem infEmb_continuous {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) : Continuous θ :=
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.continuous_of_ringHom (R := Ainf F) θ hθ.2

theorem infEmb_sigR (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (z : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ z) = starRingEnd ℂ (θ z) := by
  haveI := h.1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : sigR (Ainf F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
    rw [e, infEmb_tmul h hθ, infEmb_tmul h hθ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, h.2.2.2]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem infEmb_bijective (h : IsCMExt F E σ) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    Function.Bijective fun (z : Ainf F ⊗[F] E) (ρ : I) => θ ρ z := by
  haveI := h.1
  haveI := h.2.1
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x) := h.2.2.2
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc1 : c ≠ 1 := fun e => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, e, AlgEquiv.one_apply]
  choose θ₀ h1 h2 using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := fun φ => by
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by simp only [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · exact absurd ⟨i, by rw [← e]; ext x; simp⟩ hn
  have hb := GlobalTheory.InfAdeleCM.bijective c h.2.2.1 hc1 hc θ₀
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ₀ φ) (h1 φ) (h2 φ)) _ hΨ
  have hinj : Function.Injective τ := fun i j e => hτ.1 (by simp only [e])
  have e0 : ∀ ρ, θ ρ = θ₀ (τ ρ) := fun ρ => infEmb_unique h (hθ ρ) ⟨h1 _, h2 _⟩
  have := ((Equiv.ofInjective τ hinj).symm.arrowCongr (Equiv.refl ℂ)).bijective.comp hb
  convert this using 1
  funext z ρ
  rw [e0]
  rfl

theorem exists_compact_adele (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (R : ℝ) (C : Set (Af F ⊗[F] E))
    (hC : IsCompact C) : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z ∈ C →
      (∀ ρ, ‖θ ρ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)‖ ≤ R) → z ∈ K := by
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
  let Φ := (Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho
  have hB : IsCompact (Φ ⁻¹' Set.pi Set.univ fun _ : I => Metric.closedBall (0 : ℂ) R) :=
    Φ.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨_, (hB.prod hC).image hc, fun z hz hR => ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩⟩
  · rw [(he z).1]
    exact fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ)
  · rw [(he z).2]
    exact hz

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_infMat {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    Continuous fun h => infMat σ J θ h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact (h1.matrix_map (GlobalTheory.Member.Arch.continuous_inf F E)).matrix_map (infEmb_continuous hθ)

theorem continuous_finMat : Continuous fun h => finMat σ J h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact h1.matrix_map (GlobalTheory.LevelOpen.continuous_fin F E)

theorem JR_map {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    (JR (F := F) (Ainf F) J).map θ = J.map τ :=
  Matrix.ext fun _ _ => hθ.1 _

theorem infMat_unitary (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (g : HA (AF F) σ J) : (infMat σ J θ g)ᴴ * J.map τ * infMat σ J θ g = J.map τ := by
  have hm := GlobalTheory.Member.Arch.inf_mem σ J (HA.mat (AF F) σ J g) g.2
  have h2 := GlobalTheory.Member.Arch.form_map _ θ (infEmb_sigR h hθ)
    ((HA.mat (AF F) σ J g).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) (JR (Ainf F) J)
  rw [← JR_map J hθ]
  exact h2.symm.trans (congrArg (fun X => X.map θ) hm)

theorem exists_real_point (h : IsCMExt F E σ) (hJ : J.det ≠ 0) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (u : I → Matrix (Fin M) (Fin M) ℂ)
    (hu : ∀ ρ, (u ρ)ᴴ * J.map (τ ρ) * u ρ = J.map (τ ρ)) :
    ∃ g : HA (AF F) σ J, finMat σ J g = 1 ∧ ∀ ρ, infMat σ J (θ ρ) g = u ρ := by
  obtain ⟨a, ha, hau⟩ := GlobalTheory.Member.Arch.exists_lift (sigR (Ainf F) σ) θ (infEmb_bijective h hτ hθ)
    (fun ρ => infEmb_sigR h (hθ ρ)) (JR (Ainf F) J) (fun ρ => by
      rw [JR_map J (hθ ρ)]
      have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
      rw [this]
      exact (map_ne_zero (τ ρ)).2 hJ) u (fun ρ => by rw [JR_map J (hθ ρ)]; exact hu ρ)
  let p := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let q := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y, p x = p y → q x = q y → x = y := fun x y h1 h2 =>
    e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))
  have hs : ∀ a b, ∃ x, p x = a ∧ q x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue p q hi hs a 1
  have hg : g ∈ HR (AF F) σ J := by
    refine (GlobalTheory.UnitarySplit.mem_iff p q hi (sigR _ σ) (sigR _ σ) (sigR _ σ) (GlobalTheory.UnitarySplit.map_sig _ _)
      (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g).2 ⟨?_, ?_⟩
    · rw [g1, GlobalTheory.UnitarySplit.map_JR]
      exact ha
    · rw [g2]
      exact one_mem _
  refine ⟨⟨g, hg⟩, congrArg Units.val g2, fun ρ => ?_⟩
  rw [← hau, ← g1]
  rfl

variable (σ) in

def stab (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | StabHat F L (finMat σ J h)}
  one_mem' := fun y => by rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]

theorem isOpen_stab (L : Submodule (𝓞 E) (Fin M → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) : IsOpen (stab σ J L : Set (HA (AF F) σ J)) := by
  have := Unfold.topGroupHA σ J
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds F E M L hfg hsp 1 one_pos
  have hc := continuous_finMat (σ := σ) J
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [finMat_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, finMat_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_)
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one,
      Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end Chart

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isCMExt (cm : CMData F E) : IsCMExt F E cm.sig :=
  ⟨cm.totReal, cm.cmUnram.1, cm.deg2, cm.cmUnram.2.1⟩

theorem isHermND (cm : CMData F E) (W : HSpace E) : IsHermND cm.sig W.gram :=
  ⟨fun i j => W.herm.eq (W.frame j) (W.frame i), GlobalTheory.StabCompact.det_gram_ne_zero W⟩

theorem exists_lattice (W : HSpace E) : ∃ L : Submodule (𝓞 E) (Fin W.rank → E), L.FG ∧
    Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ ∧ (L : Set (Fin W.rank → E)) = latC W := by
  let f := W.frame.equivFun.toLinearMap
  refine ⟨W.L0.map (f.restrictScalars (𝓞 E)), W.standardTuple_isLattice.fg.map _, ?_, ?_⟩
  · have : (W.L0.map (f.restrictScalars (𝓞 E)) : Set (Fin W.rank → E)) = f '' W.L0 := rfl
    rw [this, ← Submodule.map_span, W.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, W.frame.equivFun x i • W.frame i ∈ W.L0
      rwa [W.frame.sum_equivFun]
    · intro hv
      refine ⟨W.frame.equivFun.symm v, ?_, W.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv

end Main

end GlobalTheory.Mem.VolExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactImageEqUniv
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Cocompact

theorem isOpenMap_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) :
    IsOpenMap (mk Γ) := by
  intro U hU
  have h : mk Γ ⁻¹' (mk Γ '' U) = ⋃ γ : Γ, (fun x => ((γ : G))⁻¹ * x) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, e⟩
      obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
      exact ⟨γ, by simpa using hy⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨_, hγ, mk_eq_iff.2 ⟨γ, by simp⟩⟩
  refine isOpen_coinduced.2 ?_
  change IsOpen (mk Γ ⁻¹' (mk Γ '' U))
  rw [h]
  exact isOpen_iUnion fun γ => hU.preimage (by fun_prop)

theorem exists_compact_image_eq_univ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (Quot Γ)] :
    ∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => mk Γ '' interior (K x))
    (fun x => isOpenMap_mk Γ _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, Set.eq_univ_of_forall fun q => ?_⟩
  obtain ⟨x, hx, y, hy, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hy⟩, e⟩

theorem cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CompactSpace (Quot Γ) → IsFiniteMeasure (quotMeasure Γ μ) ∧ (∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ) ∧ ∀ φ : G → ℂ, LeftInv Γ φ → Continuous φ → MemL2Quotient Γ μ φ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ hc
  obtain ⟨C, hC, hCe⟩ := exists_compact_image_eq_univ Γ
  have hfin : IsFiniteMeasure (quotMeasure Γ μ) :=
    ⟨(quotMeasure_le MeasurableSet.univ hCe.ge).trans_lt hC.measure_lt_top⟩
  refine ⟨hfin, ⟨C, hC, hCe⟩, fun φ hφ hcont => ⟨hφ, ?_⟩⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound ?_ B (Filter.Eventually.of_forall fun q => ?_)
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hφ.lift_descend]
    exact hcont.aestronglyMeasurable
  · obtain ⟨x, hx, rfl⟩ := hCe.ge (Set.mem_univ q)
    rw [hφ.descend_mk]
    exact hB x hx

end GlobalTheory.AutomorphicL2Cocompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series GlobalTheory.T.model_parameter_series_deriv_transport p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex p g.lam _ (sgStar g.abelian₂) hF hσ (GlobalTheory.T.frobeniusStickelberger_taylor_defect_eq_zero GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines GlobalTheory.T.frobeniusStickelbergerDeterminantDefect_on_line GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine GlobalTheory.T.det_column_operations_model_parameter p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology

namespace GlobalTheory.AutomorphicL2KernelContinuous

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ}

theorem finite_contributing (hc : HasCompactSupport f) {C C' : Set G} (hC : IsCompact C) (hC' : IsCompact C') :
    {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite := by
  have hK := (hC.prod (hc.isCompact.prod hC')).image (f := fun p : G × G × G => p.1 * p.2.1 * p.2.2⁻¹) (by fun_prop)
  refine (finite_mem_compact (Γ := Γ) hK).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  exact ⟨(x, x⁻¹ * γ * y, y), ⟨hx, subset_tsupport f h, hy⟩, by simp [mul_assoc]⟩

theorem locallyFinite_support [LocallyCompactSpace G] (hc : HasCompactSupport f) :
    LocallyFinite fun γ : Γ => Function.support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  rintro ⟨x, y⟩
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C', hC', hy⟩ := exists_compact_mem_nhds y
  refine ⟨C ×ˢ C', prod_mem_nhds hx hy, (finite_contributing hc hC hC').subset ?_⟩
  rintro γ ⟨p, h, h1, h2⟩
  exact ⟨p.1, h1, p.2, h2, h⟩

theorem continuous_kernel [LocallyCompactSpace G] (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous fun p : G × G => kernel Γ f p.1 p.2 := by
  have h : Continuous fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2) :=
    continuous_finsum (fun γ => by fun_prop) (locallyFinite_support hc)
  refine h.congr fun p => ?_
  exact (tsum_eq_finsum (finite_support_kernel hc p.1 p.2)).symm

theorem kernel_locallyFinite_continuous :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      (Γ : Subgroup G) [DiscreteTopology Γ] (f : G → ℂ), Continuous f → HasCompactSupport f →
      (∀ C C' : Set G, IsCompact C → IsCompact C' → {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite) ∧
        Continuous (fun p : G × G => kernel Γ f p.1 p.2) ∧ Continuous (orbitSum Γ f) := by
  intro G _ _ _ _ _ Γ _ f hf hc
  refine ⟨fun C C' hC hC' => finite_contributing hc hC hC', continuous_kernel hf hc, ?_⟩
  refine ((continuous_kernel (Γ := Γ) hf hc).comp (continuous_const.prodMk continuous_id :
    Continuous fun x : G => ((1 : G), x))).congr fun x => ?_
  simp [kernel, orbitSum]

end GlobalTheory.AutomorphicL2KernelContinuous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationCommHeisenbergIntertwinerStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) M₁ M₁') F) = Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) M₂ M₂') (W.Om g g' F) := by
  first | exact @GlobalTheory.WeilInter.om_iop | exact GlobalTheory.WeilInter.om_iop | (intros; apply GlobalTheory.WeilInter.om_iop <;> assumption)
end

