import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLatticeIsometryEqProdLocalComponents
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TwistPC

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ (J.mulVec y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A)
    (M : Matrix (Fin m) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J' (M.mulVec x) (M.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ M * J' * M) x y := by
  rw [hform_eq, hform_eq]
  have e : τ ∘ M.mulVec x = (M.map τ).mulVec (τ ∘ x) := by
    funext i; exact RingHom.map_mulVec τ M x i
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem comm_comm' (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F (Fv F v) E (Algebra.TensorProduct.comm F E (Fv F v) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_comm'' (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.comm F E (Fv F v) (Algebra.TensorProduct.comm F (Fv F v) E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem comm_sigR' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F E (Fv F v) (Formalism.UG.sigR σ (Fv F v) x) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Algebra.TensorProduct.comm F E (Fv F v) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem locData (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r' → E)) (v : HeightOneSpectrum (𝓞 F))
    (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v)) (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v))
    (k1 : jv * jv' = 1) (k2 : jv' * jv = 1)
    (hiso : Formalism.UG.cT (Formalism.UG.sigR σ (Fv F v)) jv * J'.map (Formalism.UG.inclE (F := F) (Fv F v)) * jv =
      J.map (Formalism.UG.inclE (F := F) (Fv F v)))
    (hlat : jv.mulVec '' (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v)) =
      (Formalism.L2.Herm.locL v Λ' : Set (Fin r' → E ⊗[F] Fv F v))) :
    ∃ jl : GLoc σ J v ≃ₜ* GLoc σ J' v, IsLatticeConj Λ Λ' jl ∧ ∀ g,
      (GlobalTheory.AdelicU.matHom _ σ J' (jl g)).val =
        jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * (GlobalTheory.AdelicU.matHom _ σ J g).val *
          jv'.map (Algebra.TensorProduct.comm F E (Fv F v)) := by
  obtain ⟨cm, hcm⟩ : ∃ cm : E ⊗[F] Fv F v →+* Fv F v ⊗[F] E,
      cm = (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : Fv F v ⊗[F] E →+* E ⊗[F] Fv F v,
      cb = (Algebra.TensorProduct.comm F (Fv F v) E).toRingEquiv.toRingHom := ⟨_, rfl⟩
  have ecm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      X.map (Algebra.TensorProduct.comm F E (Fv F v)) = X.map cm := by
    intro m k X; subst hcm; rfl
  have bc1 : ∀ x, cb (cm x) = x := fun x => by subst hcm hcb; exact comm_comm' v x
  have bc2 : ∀ x, cm (cb x) = x := fun x => by subst hcm hcb; exact comm_comm'' v x
  have bcm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)), (X.map cm).map cb = X := by
    intro m k X; ext i l; exact bc1 _
  simp only [ecm]
  have hab : jv.map cm * jv'.map cm = 1 := by rw [← Matrix.map_mul, k1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hba : jv'.map cm * jv.map cm = 1 := by rw [← Matrix.map_mul, k2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (jv.map cm) * JR (F := F) (Fv F v) J' * jv.map cm =
      JR (F := F) (Fv F v) J := by
    have e := congrArg (fun X => X.map cm) hiso
    simp only [Matrix.map_mul] at e
    convert e using 3
    · ext i k; subst hcm; exact (comm_sigR' σ v _).symm
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry σ J J' v _ _ hab hba hJ
  refine ⟨φ, ?_, hφ⟩
  have injv : Function.Injective jv.mulVec := fun x y hxy => by
    have := congrArg jv'.mulVec hxy
    simpa [Matrix.mulVec_mulVec, k2] using this
  have hA : (jv.map cm).map cb = jv := bcm jv
  refine ⟨LinearEquiv.ofLinear (Matrix.mulVecLin (jv.map cm)) (Matrix.mulVecLin (jv'.map cm))
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hab])
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hba]), fun y y' => ?_, fun y => ?_, fun g y => ?_⟩
  · show GlobalTheory.AdelicU.hLin σ J' (Fv F v) ((jv.map cm).mulVec y) ((jv.map cm).mulVec y') = GlobalTheory.AdelicU.hLin σ J (Fv F v) y y'
    unfold GlobalTheory.AdelicU.hLin hR
    rw [hform_mulVec, hJ]
  · show (jv.map cm).mulVec y ∈ GlobalTheory.AdelicU.latLoc F Λ' v ↔ y ∈ GlobalTheory.AdelicU.latLoc F Λ v
    have ecb : ∀ {m : ℕ} (z : Fin m → Fv F v ⊗[F] E),
        (fun i => Algebra.TensorProduct.comm F (Fv F v) E (z i)) = cb ∘ z := by
      intro m z; subst hcb; rfl
    rw [GlobalTheory.T.mem_localLatticeCompletion_iff_comm_mem, GlobalTheory.T.mem_localLatticeCompletion_iff_comm_mem, ecb, ecb]
    have e : cb ∘ (jv.map cm).mulVec y = jv.mulVec (cb ∘ y) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hA]
    rw [e]
    have := injv.mem_set_image (s := (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v))) (a := cb ∘ y)
    rw [hlat] at this
    exact this
  · show (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val.mulVec ((jv.map cm).mulVec y) =
      (jv.map cm).mulVec ((GlobalTheory.AdelicU.matHom _ σ J g).val.mulVec y)
    rw [hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hba, Matrix.mul_one]

theorem assemble (v : HeightOneSpectrum (𝓞 F)) {r r' : ℕ} (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v))
    (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v)) (M : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)) :
    jv * M.map (Algebra.TensorProduct.comm F (Fv F v) E) * jv' =
      (jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * M * jv'.map (Algebra.TensorProduct.comm F E (Fv F v))).map
        (Algebra.TensorProduct.comm F (Fv F v) E) := by
  have e : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      (X.map (Algebra.TensorProduct.comm F E (Fv F v))).map (Algebra.TensorProduct.comm F (Fv F v) E) = X := by
    intro m k X; ext i l; exact comm_comm' v _
  rw [Matrix.map_mul, Matrix.map_mul, e, e]

end Gen

set_option maxHeartbeats 3000000 in

theorem isom_locComponents : ∀ (D : D7) (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V' (frameLat V) (frameLat V') j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ₀ → ∃ jl : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (jl v)) ∧ ∀ v g, Φ₀ (locFin V v g) = locFin V' v (jl v g) := by
  intro D V V' j Φ₀ hj hΦ
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  have key := fun v => locData D.sp.cm.sig V.gram V'.gram (frameLat V) (frameLat V') v
    (j.map (Formalism.UG.prV (E := D.host.E) v)) (j'.map (Formalism.UG.prV (E := D.host.E) v))
    (GlobalTheory.HeckeTrans.map_mul_one _ h1) (GlobalTheory.HeckeTrans.map_mul_one _ h2)
    (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).1.2 (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).2
  choose jl hjl hjm using key
  refine ⟨jl, hjl, fun v g => ?_⟩
  apply GlobalTheory.T.finiteAdelicUnitaryPoint_ext_localComponents
  intro u
  have hc := hΦ (locFin V v g)
  have e1 := congrArg (fun X => GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul X j') hc
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul, Matrix.mul_assoc, h1, Matrix.mul_one] at e1
  rw [e1, Matrix.map_mul, Matrix.map_mul]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V u g, GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V' u (jl u g), hjm]
    rw [← Matrix.mul_assoc]
    exact assemble (F := D.host.F) (E := D.host.E) u _ _ _
  · rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V hu, GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V' hu, Matrix.one_mul, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.TwistPC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanIwasawaDecomposition
section
noncomputable section

namespace GlobalTheory.IwArchMin

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ}

def toC (e : A ≃+* ℂ) (b : GL (Fin n) A) : (Fin n → A) →ₛₗ[(e : A →+* ℂ)] (Fin n → ℂ) where
  toFun y := fun r => e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r)
  map_add' y z := by funext r; simp [Matrix.mulVec_add]
  map_smul' c y := by funext r; simp [Matrix.mulVec_smul]

theorem toC_apply (e : A ≃+* ℂ) (b : GL (Fin n) A) (y : Fin n → A) (r : Fin n) :
    toC e b y r = e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r) := rfl

theorem inv_mul_val (b : GL (Fin n) A) : b.1 * (b⁻¹ : GL (Fin n) A).1 = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem toC_injective (e : A ≃+* ℂ) (b : GL (Fin n) A) : Function.Injective (toC e b) := by
  intro y z h
  have h1 : (b⁻¹ : GL (Fin n) A).1 *ᵥ y = (b⁻¹ : GL (Fin n) A).1 *ᵥ z :=
    funext fun r => e.injective (congrFun h r)
  have h2 := congrArg (fun v => b.1 *ᵥ v) h1
  simpa only [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] using h2

theorem toC_mulVec (e : A ≃+* ℂ) (b M : GL (Fin n) A) (y : Fin n → A) :
    toC e b (M.1 *ᵥ y) =
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * M * b)).1 *ᵥ toC e b y := by
  funext r
  rw [toC_apply]
  have : (b⁻¹ : GL (Fin n) A).1 *ᵥ (M.1 *ᵥ y) = (b⁻¹ * M * b).1 *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) := by
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one]
  rw [this]
  exact RingHom.map_mulVec (e : A →+* ℂ) _ _ r

theorem form_conj (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (y z : Fin n → A) :
    (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) ⬝ᵥ
      ((Formalism.UG.cT σ b.1 * J * b.1) *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) = (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  funext i
  rw [Formalism.UG.cT, Matrix.vecMul_transpose]
  have := RingHom.map_mulVec σ b.1 ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i
  rw [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] at this
  exact this.symm

end Alg

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open Matrix

section Alg2

variable {A : Type} [CommRing A] {n : ℕ}

theorem jm_eq_map (e : A ≃+* ℂ) (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = (Matrix.diagonal fun i => if ε i then (1 : A) else -1).map (e : A →+* ℂ) := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
  congr 1; funext i; split_ifs <;> simp

theorem map_injective' (e : A ≃+* ℂ) {P Q : Matrix (Fin n) (Fin n) A} (h : P.map e = Q.map e) : P = Q := by
  ext i j; exact e.injective (congrFun (congrFun h i) j)

theorem exists_alg (σ : A →+* A) (e : A ≃+* ℂ) (he : ∀ x, e (σ x) = star (e x))
    (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (ε : Fin n → Bool)
    (S : Matrix (Fin n) (Fin n) A) (hSm : Formalism.REAL.Jm ε = S.map (e : A →+* ℂ)) (hb : Formalism.UG.cT σ b.1 * J * b.1 = S)
    {k : ℕ} (X : Fin (k + 1) → Submodule A (Fin n → A)) (h0 : X 0 = ⊥) (hX : Monotone X)
    (hiso : ∀ y ∈ X (Fin.last k), ∀ z ∈ X (Fin.last k), (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) = 0)
    (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ K ∈ Formalism.UG.UJ σ J, b⁻¹ * K * b ∈ Formalism.UG.UJ σ 1 ∧ ∀ i, ∀ y ∈ X i, (g * K⁻¹).1 *ᵥ y ∈ X i := by
  have hJm := hSm
  let L := toC e b
  let W : Fin (k + 1) → Submodule ℂ (Fin n → ℂ) := fun i => (X i).map L
  have hWm : Monotone W := fun i j h => Submodule.map_mono (hX h)
  have hW : GlobalTheory.FlagMeas.IsIsoFlag ε
      (fun i : Fin k => Module.finrank ℂ (W i.succ) - Module.finrank ℂ (W i.castSucc)) W := by
    refine ⟨by simp [W, h0], hWm, fun i => ?_, ?_⟩
    · have := Submodule.finrank_mono (hWm (Fin.castSucc_le_succ i)); dsimp only; omega
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      have h1 : star (L y) = fun i => e (σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) := by
        funext i; simp [L, toC_apply, he]
      have h2 : Formalism.REAL.Jm ε *ᵥ L z = fun i => e ((S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) i) := by
        funext i; rw [hJm]; exact (RingHom.map_mulVec (e : A →+* ℂ) S _ i).symm
      rw [h1, h2]
      have h3 := (RingHom.map_dotProduct (e : A →+* ℂ) (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i))
        (S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z))).symm
      refine h3.trans ?_
      rw [← hb, form_conj, hiso y hy z hz, map_zero]
  have mapForm : ∀ M : GL (Fin n) A, M ∈ Formalism.UG.UJ σ S →
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1ᴴ * Formalism.REAL.Jm ε *
        (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1 = Formalism.REAL.Jm ε := by
    intro M hM
    have hM' : Formalism.UG.cT σ M.1 * S * M.1 = S := hM
    change (M.1.map (e : A →+* ℂ))ᴴ * _ * M.1.map (e : A →+* ℂ) = _
    rw [← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul, hM']
  have hg' : b⁻¹ * g * b ∈ Formalism.UG.UJ σ S := hb ▸ GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b hg
  obtain ⟨kc, hkc, hstab⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW
    ⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩
  set K0 := Matrix.GeneralLinearGroup.map (e.symm : ℂ →+* A) kc.1 with hK0
  have hK0e : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) K0 = kc.1 := by
    ext i j; simp [K0]
  have hK0m : K0.1.map (e : A →+* ℂ) = kc.1.1 := congrArg Units.val hK0e
  have hkc2 : (kc.1.1)ᴴ * Formalism.REAL.Jm ε * kc.1.1 = Formalism.REAL.Jm ε := kc.2
  have hkc1 : (kc.1.1)ᴴ * kc.1.1 = 1 := hkc
  have hK0S : K0 ∈ Formalism.UG.UJ σ S := by
    show Formalism.UG.cT σ K0.1 * S * K0.1 = S
    apply map_injective' e
    have := hkc2
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul] at this
    exact this
  have hK01 : K0 ∈ Formalism.UG.UJ σ 1 := by
    show Formalism.UG.cT σ K0.1 * 1 * K0.1 = 1
    apply map_injective' e
    have := hkc1
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, ← Matrix.map_mul] at this
    rw [Matrix.mul_one]
    refine this.trans ?_
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  refine ⟨b * K0 * b⁻¹, ?_, ?_, fun i y hy => ?_⟩
  · have := GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b⁻¹ hK0S
    rw [inv_inv, ← hb, GlobalTheory.Core.Rk.IwArch.cT_inv_cancel] at this
    exact this
  · have : b⁻¹ * (b * K0 * b⁻¹) * b = K0 := by group
    rw [this]; exact hK01
  · have hy' : L y ∈ W i := Submodule.mem_map_of_mem hy
    have h4 := hstab i (L y) hy'
    have e1 : Formalism.MainNotions.S.uMat (⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩ * kc⁻¹ :
        Formalism.REAL.UJ ε) = (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b)).1 := by
      have : b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b = (b⁻¹ * g * b) * K0⁻¹ := by group
      have e2 : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b) =
          Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b) * kc.1⁻¹ := by
        rw [this, map_mul (Matrix.GeneralLinearGroup.map (e : A →+* ℂ)) (b⁻¹ * g * b) K0⁻¹, map_inv, hK0e]
      rw [e2]; rfl
    rw [e1, ← toC_mulVec] at h4
    obtain ⟨z, hz, hzL⟩ := Submodule.mem_map.1 h4
    rwa [toC_injective e b hzL] at hz

end Alg2

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open scoped TensorProduct
open NumberField Matrix

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_par_mul_stabArch (hc : Formalism.BasicNotions.CMData F E) (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E hc.sig)
    (V : Formalism.BasicNotions.HSpace E) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (w : InfinitePlace F)
    (b : GL (Fin V.rank) (w.Completion ⊗[F] E)) (ε : Fin V.rank → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (g : GlobalTheory.AdelicU.GArch hc.sig V.gram w) :
    ∃ p ∈ 𝔉.par hc w.Completion, ∃ k ∈ GlobalTheory.AdelicU.stabArch hc.sig V.gram w b, g = p * k := by
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ)
  have he : ∀ x, e (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig x) = star (e x) := fun x =>
    (GlobalTheory.AdelicU.infEmb_sigR hcm τ x).symm
  let X : Fin (𝔉.k + 1) → Submodule (w.Completion ⊗[F] E) (Fin V.rank → w.Completion ⊗[F] E) :=
    fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub V w.Completion (𝔉.X i)
  have h0 : X 0 = ⊥ := by simp [X, 𝔉.zero]
  have hX : Monotone X := fun i j h => GlobalTheory.Cusp.extSub_mono V w.Completion (𝔉.strictMono.monotone h)
  have hiso : ∀ y ∈ X (Fin.last 𝔉.k), ∀ z ∈ X (Fin.last 𝔉.k),
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig (y i)) ⬝ᵥ
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram *ᵥ z) = 0 := by
    intro y hy z hz
    have hz' := GlobalTheory.Cusp.extSub_mono V w.Completion 𝔉.iso hz
    have := (GlobalTheory.Cusp.mem_extSub_perp hc V).1 hz' y hy
    rw [GlobalTheory.Cusp.hR_eq] at this
    exact this
  obtain ⟨K, hK, hK1, hp⟩ := exists_alg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) e he
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram) b ε _ (jm_eq_map e ε) hb X h0 hX hiso
    (GlobalTheory.AdelicU.matHom w.Completion hc.sig V.gram g) g.2
  let kk : GlobalTheory.AdelicU.GArch hc.sig V.gram w := ⟨K, hK⟩
  refine ⟨g * kk⁻¹, ?_, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group⟩
  refine GlobalTheory.Cusp.IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab_iff_maps.2 fun y hy => ?_
  have := hp i y hy
  exact this

end Place

end GlobalTheory.IwArchMin

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.IwArchMin

theorem iwasawa_minPar : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ w (g : GArch D.sp.cm.sig V.gram w), ∃ p ∈ PArch Φ.flag0 w,
      ∃ k ∈ stabArch D.sp.cm.sig V.gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a), g = p * k := by
  intro D V Φ L a h w g
  obtain ⟨ε, hε⟩ := h.2.2.2.1 w
  exact exists_par_mul_stabArch D.sp.cm (isCMExt_host D) _ Φ.flag0 w _ ε hε g

end GlobalTheory.IwArchMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineEqRealScalarSmulSupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanLine_eq_realScalar_smul_supported : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ),
    (∀ t : ℝ, lineAt θ τ z t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (lineAt θ τ z 1) := by
  first | exact @GlobalTheory.LineRealAd.lineAt_realAd_smul | exact GlobalTheory.LineRealAd.lineAt_realAd_smul | (intros; apply GlobalTheory.LineRealAd.lineAt_realAd_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanSupportedSmulTransposeGramFiniteSubOnStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.InfKill.smul_mat_kapX_sub_one | exact GlobalTheory.InfKill.smul_mat_kapX_sub_one | (intros; apply GlobalTheory.InfKill.smul_mat_kapX_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasicModelsOfFunctorialityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_models_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → CoreModels := by
  first | exact @GlobalTheory.SepRows.coreModels | exact GlobalTheory.SepRows.coreModels | (intros; apply GlobalTheory.SepRows.coreModels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftScalarOfInnerProductFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatum_lift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  first | exact @GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta | exact GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta | (intros; apply GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairWStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  first | exact @GlobalTheory.ArchLineContPair.continuous_apply | exact GlobalTheory.ArchLineContPair.continuous_apply | (intros; apply GlobalTheory.ArchLineContPair.continuous_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitaryStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  first | exact @GlobalTheory.AntiInvLoc.eventually_exists_antiInv | exact GlobalTheory.AntiInvLoc.eventually_exists_antiInv | (intros; apply GlobalTheory.AntiInvLoc.eventually_exists_antiInv <;> assumption)
end

