import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFrames
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchCoords

open GlobalTheory.FockVacuum in

theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_cplx_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSigna
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ArchCoordsD

open GlobalTheory.FockVacuum in

theorem herm_rot_pos {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b *
      star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

open GlobalTheory.FockVacuum in

theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_rot_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoordsD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
section
set_option autoImplicit false

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option maxHeartbeats 1000000 in

theorem exists_const_rdU_of_moveMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' k k' δ h ρ ν hρ hM hone n
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  have hex : ∀ x : (U.X k).dom, ∃ (y' : FrPt Xo c (CAt σ)) (t₀ : (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' ∧
      FrBor (fun i => Option.elim i t₀ (fun _ => 1)) (U'.un k' ⟨_, h.mem_dom x.2⟩) y' := fun x => by
    obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k x)).1
    obtain ⟨t₀, ht₀⟩ := exists_frBor_gen _ y' (hM x y' hy').1 (hM x y' hy').2
    exact ⟨y', t₀, hy', ht₀⟩
  choose y' t₀ hm hb using hex
  have hla : ∀ (w : (E →+* ℂ) × ℕ → ℕ) (τ : (U'.X k').Ψ) (i : Fin r),
      Formalism.L2.PjFree.laU U' w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := fun w τ i => by
    unfold Formalism.L2.PjFree.laU
    rw [h.p0]
  have key : ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x : (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n *
        Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) := fun w hD f hf f' hf' hv x => by
    have v1 : Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (evR Xo c f' (U.un k x)) := dif_pos x.2
    have v2 : Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) =
      Formalism.L2.PjFree.toC (evR Xo c f (U'.un k' ⟨_, h.mem_dom x.2⟩)) := dif_pos (h.mem_dom x.2)
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf _ _ (y' x) (hb x)
    have v4 : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
        Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (((fun i => Option.elim i (t₀ x) (fun _ => 1) : Ix Dw → (CAt σ)ˣ) j : (CAt σ)ˣ) : CAt σ) ^ ex Dw w n j := rfl
      rw [this, Finset.prod_eq_single none]
      · rfl
      · rintro (_ | j) _ hj
        · exact (hj rfl).elim
        · exact one_pow _
      · intro hn; exact (hn (Finset.mem_univ _)).elim
    rw [v1, v2, hv _ _ (hm x), v3, ← v4]
    rfl
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.exists_norm_one_const_ratio_of_common_ratio (Frame (U.X k).Ψ r)
    {p : ((E →+* ℂ) × ℕ → ℕ) × Rul Xo c × Rul Xo c // Dom p.1 n ∧ p.2.1 ∈ sec Xo c p.1 n ∧ p.2.2 ∈ sec Xo c p.1 n ∧
      ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c p.2.2 y = evR Xo c p.2.1 y'}
    (U.X k).dom (FourierCoefficientDomain.isOpen_dom _) (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected
    (fun i => Formalism.L2.PjFree.rdU U i.1.2.2 k)
    (fun i x => Formalism.L2.PjFree.rdU U' i.1.2.1 k' (lact δ (castFr h.psi x)))
    (fun x => if hx : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (t₀ ⟨x, hx⟩ : CAt σ) ^ n else 0)
    (fun i => (hU.2.2.2.2.1 _ n i.2.1 _ i.2.2.2.1 k).1)
    (fun i => (hU'.2.2.2.2.1 _ n i.2.1 _ i.2.2.1 k').1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn fun x hx => h.mem_dom hx)
    (fun i x hx => by
      rw [dif_pos hx]
      exact key _ i.2.1 _ i.2.2.1 _ i.2.2.2.1 i.2.2.2.2 ⟨x, hx⟩)
    (fun ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      have hsec := hU.2.2.2.2.1 w n hD f' hf' k
      have hQ := hU'.2.2.2.2.1 w n hD f hf k'
      have h1 : ‖Formalism.L2.PjFree.toC (t₀ x₀ : CAt σ)‖ = 1 := hone x₀ _ _ hx₀ (hm x₀) (hb x₀)
      have v5 := congrArg norm (key w hD f hf f' hf' hv x₀)
      rw [norm_mul, norm_pow, h1, one_pow, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (hla w), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact ⟨ε, hε, fun w hD f hf f' hf' hv x hx => hc ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx⟩

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem epi_of_isPullback_galois {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (hc : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {a : P ⟶ X} {b : P ⟶ Q} {c : Q ⟶ Y} (h : IsPullback a b π c) : Epi b := by
  have e := h.flip.isoPullback_hom_fst
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst hc c
  rw [← e]
  exact epi_comp _ _

variable {S : Scheme.{0}}

theorem isPullback_whiskerRight_fst {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.fst A.hom B.hom) (ψ ▷ B).left ψ.left (pullback.fst A'.hom B.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd A'.hom B.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerRight_left_fst ψ).symm (IsPullback.of_hasPullback A'.hom B.hom)
  rw [Over.whiskerRight_left_snd, Over.w]
  exact IsPullback.of_hasPullback A.hom B.hom

theorem isPullback_whiskerLeft_snd {A A' : Over S} (ψ : A ⟶ A') (B : Over S) :
    IsPullback (pullback.snd B.hom A.hom) (B ◁ ψ).left ψ.left (pullback.snd B.hom A'.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst B.hom A'.hom) (v₂₂ := A'.hom) (h₃₁ := B.hom) ?_
    (Over.whiskerLeft_left_snd ψ).symm (IsPullback.of_hasPullback B.hom A'.hom).flip
  rw [Over.whiskerLeft_left_fst, Over.w]
  exact (IsPullback.of_hasPullback B.hom A.hom).flip

theorem exists_desc_endo (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A') (hψ : IsMonHom ψ)
    (hc : GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left)
    (f : A ⟶ A) (hf : IsMonHom f) (hH : ∀ h ∈ H, h ≫ f ∈ H) :
    ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by

  have kill : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hc.inv ⟨h, hh⟩)
  have inv : ∀ a : H, (transl a.1).left ≫ f.left ≫ ψ.left = f.left ≫ ψ.left := by
    intro a
    have e : transl a.1 ≫ f ≫ ψ = f ≫ ψ := by
      have k1 : toUnit A ≫ a.1 ≫ f ≫ ψ = 1 := by
        rw [← Category.assoc a.1, kill _ (hH _ a.2), comp_one]
      rw [transl, MonObj.mul_comp, Category.id_comp, Category.assoc, k1, _root_.mul_one]
    simpa using congrArg Over.Hom.left e
  obtain ⟨g, hg, -⟩ := hc.existsUnique_desc (f.left ≫ ψ.left) inv
  have hepi := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hc
  have gw : g ≫ A'.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ A' := Over.homMk g gw
  have hf' : ψ ≫ f' = f ≫ ψ := Over.OverMorphism.ext (by simpa [f'] using hg)
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', ← Category.assoc, IsMonHom.one_hom f]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback_galois hc (isPullback_whiskerRight_fst ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback_galois hc (isPullback_whiskerLeft_snd ψ A')
    have : Epi (ψ ⊗ₘ ψ) := by
      rw [MonoidalCategory.tensorHom_def]
      have := Over.epi_of_epi_left (ψ ▷ A)
      have := Over.epi_of_epi_left (A' ◁ ψ)
      exact epi_comp _ _
    rw [← cancel_epi (ψ ⊗ₘ ψ), ← reassoc_of% (IsMonHom.mul_hom ψ), hf', ← Category.assoc,
      IsMonHom.mul_hom f, Category.assoc, IsMonHom.mul_hom ψ]
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hf']

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HomDescent

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft' (A : Over S) {Y Z : Over S} (q : Y ⟶ Z) :
    IsPullback (A ◁ q).left (snd A Y).left (snd A Z).left q.left := by
  have h1 : IsPullback (fst A Z).left (snd A Z).left A.hom Z.hom := IsPullback.of_hasPullback A.hom Z.hom
  have h2 : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback A.hom Y.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight' {A A' : Over S} (q : A ⟶ A') (Y : Over S) :
    IsPullback (q ▷ Y).left (fst A Y).left (fst A' Y).left q.left := by
  have h1 : IsPullback (snd A' Y).left (fst A' Y).left Y.hom A'.hom :=
    (IsPullback.of_hasPullback A'.hom Y.hom).flip
  have h2 : IsPullback (snd A Y).left (fst A Y).left Y.hom A.hom := (IsPullback.of_hasPullback A.hom Y.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem epi_of_isPullback {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {u : P ⟶ Q} {v : P ⟶ X} {t : Q ⟶ Y} (hp : IsPullback u v t π) : Epi u := by
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst h t
  rw [← hp.isoPullback_hom_fst]
  infer_instance

theorem exists_desc : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  intro S A A' B _ _ _ _ _ H ψ hψ hG f hf hH
  have inv : ∀ a : H, (GlobalTheory.UPel.HT.Hecke.transl a.1).left ≫ f.left = f.left := by
    intro a
    rw [← Over.comp_left]
    congr 1
    rw [GlobalTheory.UPel.HT.Hecke.transl, mul_comp, Category.id_comp, Category.assoc, hH a.1 a.2, comp_one, _root_.mul_one]
  obtain ⟨g, hg, -⟩ := hG.existsUnique_desc f.left inv
  have eψ : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG
  have w : g ≫ B.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ B := Over.homMk g w
  have hf' : ψ ≫ f' = f := Over.OverMorphism.ext hg
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', IsMonHom.one_hom]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback hG (isPullback_whiskerRight' ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback hG (isPullback_whiskerLeft' A' ψ)
    have e : Epi (ψ ⊗ₘ ψ).left := by
      rw [MonoidalCategory.tensorHom_def, Over.comp_left]; infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (ψ ⊗ₘ ψ).left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Category.assoc, ← IsMonHom.mul_hom ψ, Category.assoc, hf', IsMonHom.mul_hom, ← hf',
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

end GlobalTheory.HomDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFramesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fock_vacuum_gaussian_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → Framed τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix P Q) (b : Ix R S) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.FockVacuum.exists_vacuum | exact GlobalTheory.FockVacuum.exists_vacuum | (intros; apply GlobalTheory.FockVacuum.exists_vacuum <;> assumption)
end

