import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem thetaV_eq_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.thetaV I v y = θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) y) := by
  have hb : ∀ b : Ainf I.F,
      InfinitePlace.Completion.extensionEmbedding v (b v) = θ' (b ⊗ₜ[I.F] (1 : I.E)) := by
    intro b
    have hc : Continuous fun b : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (b v) :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
    refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hc hθ'.2 (funext fun x => ?_)) b
    show InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F (Ainf I.F) x v) =
      θ' ((algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E))
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul x, hθ'.1, I.φ_over]
    exact Formalism.L2.SG.AdBridge.evV_algebraMap I v x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul, Algebra.TensorProduct.map_tmul]
    have e : (fstA I.F a) ⊗ₜ[I.F] ((AlgHom.id I.F I.E) x) =
        ((fstA I.F a) ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    rw [e, map_mul, hθ'.1, ← hb]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (k : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I k).map (Formalism.L2.SG.AdBridge.thetaV I v) = Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ' k := by
  ext i j
  exact thetaV_eq_gen I v θ' hθ' _

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem tauF_eq_comm (I : Formalism.MainNotions.S.AutInst) (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I y = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E
      (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem ofHAFin_eq_one (I : Formalism.MainNotions.S.AutInst) (k : Formalism.L2.SG.AdBridge.HAd I)
    (h : (Formalism.L2.SG.AdBridge.hmat I k).map (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E)) = 1) :
    Formalism.L2.SG.AdBridge.ofHAFin I k = 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at e
  simp only [Formalism.L2.SG.AdBridge.ofHAFin, Matrix.map_apply, tauF_eq_comm, e, Matrix.one_apply]
  split_ifs <;> simp

theorem infMat_of_mem_GfC {D : D7} (k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0))
    (θ' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram θ' k = 1 := by
  have e : (infHom (D.sp.Y 0) k).val = 1 := by
    rw [show infHom (D.sp.Y 0) k = 1 from hk]; rfl
  ext i j
  have e2 := congrFun (congrFun e i) j
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_apply, Matrix.map_apply]
  refine (congrArg θ' e2).trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_GfC_of_infMat {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (k : GA D (D.sp.Y 0))
    (hk : ∀ τ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram (θ τ) k = 1) : k ∈ GfC (D.sp.Y 0) := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  obtain ⟨h1, -⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.Y 0)).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  exact h1 k fun σ => hk (r σ)

theorem conj_eq_iff {n : ℕ} (P M N : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    P⁻¹ * M * P = N ↔ M = P * N * P⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  constructor
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem isAtTau_atTau {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) : IsAtTau θ (D.sp.Y 0) τ g (atTau θ (D.sp.Y 0) τ g) := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau (D.sp.Y 0) τ θ hθ g hg
  unfold atTau
  rw [dif_pos hu.exists]
  exact hu.exists.choose_spec

theorem iota_real_finite_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hι : ∀ x : I.E, HEq (ιE x) x) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (ι k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ pl.symm τ → (ι (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  intro ι
  subst h
  have hι' : ∀ x, ιE x = x := fun x => eq_of_heq (hι x)
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := by
    ext v
    have e1 : embS D (pl v) = embS D ((Formalism.L2.Host.tauPl D).symm v) := by
      ext x
      exact (congrArg (embS D (pl v)) (hι' x).symm).trans (hφ v x).symm
    exact GlobalTheory.PointAtPlace.tauE_injective e1
  subst hpl
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit

  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  refine ⟨fun k => ⟨fun hk => ?_, fun hk => ?_⟩, ?_, ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · apply mem_GfC_of_infMat θ hθ k
    intro τ
    have e := hinf k (Formalism.L2.Host.tauPl D τ)
    rw [congrFun hk (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply] at e
    have e2 := (conj_eq_iff _ _ _ (hPu _)).1 e.symm
    refine e2.trans ?_
    rw [show Formalism.MainNotions.S.uMat ((1 : (Formalism.L2.SG.InstExistsPf.instOf D).Ginf) (Formalism.L2.Host.tauPl D τ)) = 1 from rfl,
      Matrix.mul_one]
    exact Matrix.mul_nonsing_inv _ (hd _)
  · intro τ g hg
    have hat := isAtTau_atTau θ hθ τ g hg
    refine ⟨?_, fun v hv => ?_, ?_⟩
    · apply Subtype.ext
      apply Units.ext
      have e := (key (atTau θ (D.sp.Y 0) τ g)).2
      refine e.trans (ofHAFin_eq_one _ _ ?_)
      · have e3 : (finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g)).val = 1 := by
          rw [show finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) = 1 from hat.1]; rfl
        ext i j
        exact congrFun (congrFun e3 i) j
    · apply Subtype.ext
      apply Units.ext
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 v) = 1
      rw [hinf _ v]
      have hne : (Formalism.L2.Host.tauPl D).symm v ≠ τ := fun e => hv ((Equiv.symm_apply_eq _).1 e)
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ ((Formalism.L2.Host.tauPl D).symm v)) (atTau θ (D.sp.Y 0) τ g) = 1 := hat.2.2 _ hne
      rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
    · apply heq_of_eq
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (Formalism.L2.Host.tauPl D τ)) = _
      rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ τ) (atTau θ (D.sp.Y 0) τ g) = g := hat.2.1
      rw [e]
      rfl
  · intro τ y
    set P := (Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ) with hP
    have hdP : IsUnit P.det := hd _
    set H : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      gramAt D (D.sp.Y 0) τ with hH
    set Y : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      Formalism.MainNotions.S.uMat y with hY
    have hs : Pᴴ * H * P = Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := by
      have := (Formalism.L2.SG.InstExistsPf.instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
      have eφ : (Formalism.L2.SG.InstExistsPf.instOf D).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
        show embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ)) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [eφ] at this
      exact this
    have hy : Yᴴ * Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) * Y =
        Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := y.2
    have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdP
    have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
    have hg : (P * Y * P⁻¹)ᴴ * H * (P * Y * P⁻¹) = H := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc (P⁻¹)ᴴ * (Yᴴ * Pᴴ) * H * (P * Y * P⁻¹) = (P⁻¹)ᴴ * (Yᴴ * (Pᴴ * H * P) * Y) * P⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * H * P) * P⁻¹ := by rw [hs, hy]
        _ = H := by
            simp only [Matrix.mul_assoc]
            rw [hPi, Matrix.mul_one, ← Matrix.mul_assoc, hPiH, Matrix.one_mul]
    refine ⟨P * Y * P⁻¹, hg, ?_⟩
    have hat := isAtTau_atTau θ hθ τ (P * Y * P⁻¹) hg
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹))).1 (Formalism.L2.Host.tauPl D τ)) = Y
    rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ τ) (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹)) = P * Y * P⁻¹ := hat.2.1
    rw [e]
    exact (conj_eq_iff _ _ _ (hPu _)).2 rfl

theorem iotaX_real_finite : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod hιE
  exact iota_real_finite_of_eq R.θ hMod.inf X.B.I h X.ιE X.pl X.φ_eq hιE

end GlobalTheory.IotaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatum
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjLiftData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_galConj_mu (R : RealDat D A Ks) (hL : R.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (μ' : (AE D)ˣ →* Circle) (hμ : ChiAt R i σ μ') :
    ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add, RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hL.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hL.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

theorem exists_galConj_eta (R : RealDat D A Ks) (hL : R.Is A.μ0) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (η' : (AE D)ˣ →* Circle) (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [GlobalTheory.EtaConjChar.twVal_half _ P (GlobalTheory.EtaConjChar.locK_eq_one hH hη.2.1 P), GlobalTheory.EtaConjChar.twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl,
    ← hL.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl, ← hy1, ← hy2, hσ.1]

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q : Finset (Pl D.host.E)} (hQ : Q = ∅) (s : ℂ →+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    s ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ => χ, ξ⟩ x : ℂˣ) : ℂ) =
      ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (Units.map s.toMonoidHom).comp (χ PP), ξ'⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp [h1]

theorem is_congr {Γ Gr W : Type} [Group Γ] [Group Gr] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gr}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gr} (hJ : J = J') {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    (h : ∀ x hx hx', χ ⟨x, hx⟩ = χ' ⟨x, hx'⟩) {I : Type} [Fintype I] {y : I → Gr} {H : HMod (Gr → W)}
    (hH : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) : H.Is (Bridge.AdForms ι ρ J' χ') (Bridge.adInner ι J' y) := by
  subst hJ
  obtain rfl : χ = χ' := MonoidHom.ext fun x => h x.1 x.2 x.2
  exact hH

set_option maxHeartbeats 1000000 in

theorem isLiftDataC_of_liftData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L _ i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hL
  classical
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨s, hs⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL D.what₂.embLL σ
  have hE : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  obtain ⟨hω, hvec, hio, -⟩ := hL
  obtain ⟨μH, hμ1, hμ2⟩ := exists_galConj_mu R hC.lev i σ s hE μ' hμ
  obtain ⟨ηH, hη1, hη2⟩ := exists_galConj_eta R hC.lev σ s hE η' hη
  have hQ := GlobalTheory.LiftLower.Q_base hC.lev
  let m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP =>
    (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (R.chi ((i : ℕ) + 1) PP)⁻¹
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact GlobalTheory.LiftScalarCompare.primeToHost hC.lev PP hPP
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsConjChars R i A.μ0 s μ' η' m := by
    refine ⟨μH, ηH, hμ1, hη1, hμ2, hη2, fun PP hPP a k u hk hu => ?_⟩
    have hg : PP ∈ R.Pg := hPP.resolve_right (by simp [hQ])
    have h1 := hμ1 PP k
    have h2 := hC.lev.chi i PP hg a k u hk hu
    rw [hC.lev.xi_base, mul_one] at h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one] at h1
    apply Units.ext
    rw [h1, ← h2]
    rfl
  have hlv : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      (R.datWp i R.triv) (R.Q A.μ0) m f₀ f := by
    have hv := hvec.vec
    rw [hQ]
    unfold Datum.IsThPVecOf at hv
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec
    have hq : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
        Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
      intro y
      simp [Datum.omegaQ]
    simp only [GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv, hq]
    exact hv
  obtain ⟨χ', hχ, hH⟩ := hf.model
  have key : ∀ k : levJ R i A.μ0, χ' k = levFn (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)
      (Formalism.UG.bc (Lev.swapAE D) k.1.1) := fun k => Units.ext <| (hχ k).elim fun y hy =>
    hy.2.symm.trans ((hs y).symm.trans ((congrArg s hy.1).trans
      (levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hQ (s : ℂ →+* ℂ) (fun PP => (R.chi ((i : ℕ) + 1) PP)⁻¹) (R.xiR A.μ0) m _)))
  have hH' := is_congr (GlobalTheory.Survey.LevelVectorSizeBounds.grp_triv R i A.μ0 m).symm
    (χ' := GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (fun x hx _ => key ⟨x, hx⟩) hH
  refine ⟨s, m, ⟨hC, hp, hE, GlobalTheory.Survey.LevelVectorSizeBounds.isLocal_triv R, hm, hω, hvec.onb, hlv, fun P => hvec.theta P, hf.coef, hio⟩,
    hC.models.νV i A.μ0, (R.B.L i A.μ0).pres.reps, hH'⟩

end GlobalTheory.ConjLiftData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLin

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (starRingEnd D.host.E x) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem toEAf_incA_bar (c : 𝓞 D.host.E) :
    toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) =
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
  simp [toEAf, finPart, incA, inclR, Formalism.L2.DIV.oToS, Formalism.UG.inclE]
  rfl

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

variable {D : D7}

theorem tmul_smul_add (p : AF D.host.F) (c x y : D.host.E) :
    p ⊗ₜ[D.host.F] (c * x + y) = (p ⊗ₜ[D.host.F] x) * incA D c + p ⊗ₜ[D.host.F] y := by
  rw [TensorProduct.tmul_add]
  congr 1
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm x c]

theorem rowAdj_smul_add (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D)
    (u v : Fin T.rank → D.host.E) (c : D.host.E) :
    GlobalTheory.LiftDat.rowAdj T βT a e (c • u + v) =
      toEAf D (incA D (starRingEnd D.host.E c)) • GlobalTheory.LiftDat.rowAdj T βT a e u + GlobalTheory.LiftDat.rowAdj T βT a e v := by
  have hM : (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c • u + v) k) * incA D (T.gram k l)) =
      incA D (starRingEnd D.host.E c) • (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] u k) * incA D (T.gram k l)) +
      (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      tmul_smul_add, mul_add, map_add, map_mul, cA_incA, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GlobalTheory.LiftDat.rowAdj
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

theorem rowRed_smul_add : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  intro D T βT a e PP u v hu hv c
  have hz := toEAf_incA_bar (D := D) c
  have hrow := rowAdj_smul_add T βT a e u v (c : D.host.E)
  have hzi : toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hz]; exact Subtype.property _
  have hent : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j =
      toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) * GlobalTheory.LiftDat.rowAdj T βT a e u 0 j + GlobalTheory.LiftDat.rowAdj T βT a e v 0 j := by
    intro j; rw [hrow]; simp [Matrix.add_apply, Matrix.smul_apply]
  have hint : IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hent]
    exact Subring.add_mem _ (Subring.mul_mem _ hzi (hu 0 j)) (hv 0 j)
  refine ⟨hint, ?_⟩
  funext j
  simp only [GlobalTheory.LiftDat.rowRed, redM, dif_pos (hint 0 j), dif_pos (hu 0 j), dif_pos (hv 0 j)]
  have hsub : (⟨GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j, hint 0 j⟩ :
      Formalism.L2.Herm.intAf D.host.F D.host.E) =
      Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) * ⟨_, hu 0 j⟩ + ⟨_, hv 0 j⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, ← hz, hent]
  rw [hsub, map_add, map_mul, Formalism.L2.DIV.resS_oToS]

end GlobalTheory.RowLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocalStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ γ : GRat σ J, γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  first | exact @GlobalTheory.TrEll.charpoly_eq_sharp | exact GlobalTheory.TrEll.charpoly_eq_sharp | (intros; apply GlobalTheory.TrEll.charpoly_eq_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLatticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT → ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) → ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  first | exact @GlobalTheory.LevkLoc.congr_of_isAA | exact GlobalTheory.LevkLoc.congr_of_isAA | (intros; apply GlobalTheory.LevkLoc.congr_of_isAA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  first | exact @GlobalTheory.SplitRowLat.conj_mem_latHat_iff | exact GlobalTheory.SplitRowLat.conj_mem_latHat_iff | (intros; apply GlobalTheory.SplitRowLat.conj_mem_latHat_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSubStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_nrm2_om_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  first | exact @GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | exact GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub | (intros; apply GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub <;> assumption)
end

