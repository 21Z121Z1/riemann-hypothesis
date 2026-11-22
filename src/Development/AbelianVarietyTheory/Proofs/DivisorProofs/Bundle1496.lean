import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPoly

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitary
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ConjCartan

open scoped ComplexOrder in

theorem exists_conj_cartan_matrix : ∀ (n : ℕ) (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ), Mᴴ = M → IsCartan M θ₁ → IsCartan M θ₂ →
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  intro n M θ₁ θ₂ hM h1 h2
  have key : ∀ θ, IsCartan M θ → θ.map star * θ.map star = 1 ∧ (θ.map star)ᴴ * M * θ.map star = M ∧
      (M * θ.map star).PosDef := by
    rintro θ ⟨hθ, hu, hp⟩
    have hS : θ.map star = θᵀᴴ := rfl
    have hT : (θ.map star)ᴴ = θᵀ := by rw [hS, Matrix.conjTranspose_conjTranspose]
    have hSS : θ.map star * θ.map star = 1 := by
      rw [hS, ← Matrix.conjTranspose_mul, ← Matrix.transpose_mul, hθ, Matrix.transpose_one, Matrix.conjTranspose_one]
    have hMS : M * θ.map star = θᵀ * M := by
      calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [hu]
        _ = θᵀ * M := by rw [Matrix.mul_assoc _ (θ.map star), hSS, Matrix.mul_one]
    have hH : (M * θ.map star)ᴴ = M * θ.map star := by
      rw [Matrix.conjTranspose_mul, hT, hM, hMS]
    refine ⟨hSS, by rw [hT]; exact hu, ?_⟩
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x hx => ?_⟩
    have hx' : star x ≠ 0 := by simpa using hx
    have hre := hp (star x) hx'
    have e1 : star x ⬝ᵥ (M * θ.map star) *ᵥ x = (θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x) := by
      rw [star_star, hMS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : star (star x ⬝ᵥ (M * θ.map star) *ᵥ x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
      conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [Complex.lt_def]
    refine ⟨by rw [e1]; simpa using hre, ?_⟩
    have h3 := congrArg Complex.im e2
    have h4 : (star (star x ⬝ᵥ (M * θ.map star) *ᵥ x)).im = -(star x ⬝ᵥ (M * θ.map star) *ᵥ x).im :=
      Complex.conj_im _
    rw [Complex.zero_im]; linarith
  obtain ⟨hs1, hs2, hs3⟩ := key θ₁ h1
  obtain ⟨ht1, ht2, ht3⟩ := key θ₂ h2
  set S₁ := θ₁.map star
  set S₂ := θ₂.map star
  obtain ⟨p, q, B, B', hBB, hB'B, hBG, hBs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n M S₁ hs1 hs2 hs3
  set D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hDh : Dᴴ = D := by simp [D, Matrix.fromBlocks_conjTranspose]
  have hDD : D * D = 1 := by simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set T := B' * S₂ * B
  have hTT : T * T = 1 := by
    calc T * T = B' * S₂ * (B * B') * S₂ * B := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, Matrix.mul_assoc B', ht1, Matrix.mul_one, hB'B]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    have := congrArg (B'.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hB'B] using this
  have hDT : (D * T).PosDef := by
    have h := ht3.conjTranspose_mul_mul_same hinj
    have e : Bᴴ * (M * S₂) * B = D * T := by
      calc Bᴴ * (M * S₂) * B = Bᴴ * M * (B * B') * S₂ * B := by rw [hBB]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = D * T := by rw [← hBG]; simp only [T, Matrix.mul_assoc]
    rwa [e] at h
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.cartanInvolution_conj_of_posDef _ D T hDh hDD hTT hDT

  have haL : (D * aᴴ * D) * a = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc aᴴ, ha1, hDD]
  set U := B * a * B'
  set V := B * (D * aᴴ * D) * B'
  have hVU : V * U = 1 := by
    calc V * U = B * (D * aᴴ * D) * (B' * B) * a * B' := by simp only [V, U, Matrix.mul_assoc]
      _ = 1 := by rw [hB'B, Matrix.mul_one, Matrix.mul_assoc B, haL, Matrix.mul_one, hBB]
  have hUU : Uᴴ * M * U = M := by
    have hBh : B'ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc Uᴴ * M * U = B'ᴴ * (aᴴ * (Bᴴ * M * B) * a) * B' := by
          simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * (Bᴴ * M * B) * B' := by rw [hBG, ha1]
      _ = (B'ᴴ * Bᴴ) * M * (B * B') := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBh, hBB, Matrix.one_mul, Matrix.mul_one]
  have hB'S : B' * S₁ = D * B' := by
    calc B' * S₁ = B' * S₁ * (B * B') := by rw [hBB, Matrix.mul_one]
      _ = B' * (S₁ * B) * B' := by simp only [Matrix.mul_assoc]
      _ = B' * (B * D) * B' := congrArg (fun Z => B' * Z * B') hBs
      _ = (B' * B) * D * B' := by simp only [Matrix.mul_assoc]
      _ = D * B' := by rw [hB'B, Matrix.one_mul]
  have hUS : U * S₁ = S₂ * U := by
    calc U * S₁ = B * (a * D) * B' := by simp only [U, Matrix.mul_assoc, hB'S]
      _ = B * (T * a) * B' := by rw [ha2]
      _ = (B * B') * S₂ * (B * a * B') := by simp only [T, Matrix.mul_assoc]
      _ = S₂ * U := by rw [hBB, Matrix.one_mul]
  refine ⟨U.map star, V.map star, ?_, ?_, ?_⟩
  · have hUV : U * V = 1 := mul_eq_one_comm.1 hVU
    have : (U * V).map star = (1 : Matrix (Fin n) (Fin n) ℂ).map star := by rw [hUV]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).map star by simp, ← this]; ext i j; simp [Matrix.mul_apply, star_sum]
  · have e : (U.map star)ᵀ = Uᴴ := rfl
    rw [e, show (U.map star).map star = U by ext i j; simp, hUU]
  · have : (U * S₁).map star = (S₂ * U).map star := by rw [hUS]
    have e1 : (U * S₁).map star = U.map star * θ₁ := by ext i j; simp [S₁, Matrix.mul_apply, star_sum]
    have e2 : (S₂ * U).map star = θ₂ * U.map star := by ext i j; simp [S₂, Matrix.mul_apply, star_sum]
    rw [← e1, ← e2, this]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

variable (F E) in

def archIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c z hz u hu => by
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem cA_mem_archIdeal (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ archIdeal F E) : cA σ z ∈ archIdeal F E :=
  fun u hu => by rw [← map_smul, hz u hu, map_zero]

end GlobalTheory.ConjCartan

namespace GlobalTheory.ConjCartan

theorem mapMatrix_transpose {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : f.mapMatrix Aᵀ = (f.mapMatrix A)ᵀ := rfl

theorem conj_cartan_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have cm := hB.cm
  have hM : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← cm.2.2.2 (B.emb w).1, hX.herm]
  have hU := fun w => exists_conj_cartan_matrix n _ (X.θ w) (Y.θ w) (hM w) (hX.cartan w) (hY.cartan w)
  choose u v huv hun hint using hU
  choose lift hlat hlev using GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents F E σ cm B.emb
  let π := Ideal.Quotient.mk (archIdeal F E)
  let Dm : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (u w - 1) i j
  let Dv : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (v w - 1) i j
  have hDm : π.mapMatrix Dm = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDv : π.mapMatrix Dv = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDc : π.mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (cA_mem_archIdeal σ (hlat _))
  have hDmw : ∀ w, (piInf (B.emb w)).mapMatrix Dm = u w - 1 := fun w => by
    ext i j; exact hlev _ w
  have hDvw : ∀ w, (piInf (B.emb w)).mapMatrix Dv = v w - 1 := fun w => by
    ext i j; exact hlev _ w
  have zero : ∀ Z : Matrix (Fin n) (Fin n) (AE F E), π.mapMatrix Z = 0 → (∀ w, (piInf (B.emb w)).mapMatrix Z = 0) → Z = 0 := by
    intro Z h1 h2; ext i j
    exact GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents F E σ cm B.emb _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j))
      (fun w => congrFun (congrFun (h2 w) i) j)
  have hGH : (1 + Dm) * (1 + Dv) = 1 := by
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDm, hDv]; simp
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDmw, hDvw, add_sub_cancel, add_sub_cancel, huv w, sub_self]
  let g0 : GL (Fin n) (AE F E) := ⟨1 + Dm, 1 + Dv, hGH, mul_eq_one_comm.1 hGH⟩
  have hcw : ∀ w, (piInf (B.emb w)).mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = (u w).map star - 1 := fun w => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (cA σ).toRingHom (Dm i j) = cA σ (Dm i j) from rfl, GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj F E σ cm w (B.emb w)]
    simp only [Dm, Matrix.of_apply]
    rw [hlev]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, star_sub]
    split_ifs <;> simp
  have hJw : ∀ w, (piInf (B.emb w)).mapMatrix (incM F X.J) = X.J.map (B.emb w).1 := fun w => by
    ext i j; simp [incM, piInf_inclR]
  have hUG : g0 ∈ UG (cA σ) (incM F X.J) := by
    change (1 + Dm)ᵀ * incM F X.J * (cA σ).toRingHom.mapMatrix (1 + Dm) = incM F X.J
    rw [map_add, map_one]
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDm, hDc]; simp
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDmw, hcw, hJw,
        add_sub_cancel, add_sub_cancel, hun w, sub_self]
  refine ⟨⟨g0, hUG⟩, ?_, fun w => ?_⟩
  · intro a ha
    show a • ((1 + Dm) - 1) = 0
    ext i j
    simp only [add_sub_cancel_left, Matrix.smul_apply, Matrix.zero_apply]
    exact hlat _ a ha
  · have : (mat (⟨g0, hUG⟩ : UA σ X.J)).map (piInf (B.emb w)) = u w := by
      show (piInf (B.emb w)).mapMatrix (1 + Dm) = u w
      rw [map_add, map_one, hDmw]; abel
    rw [this]; exact hint w

end GlobalTheory.ConjCartan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero
section
noncomputable section

namespace GlobalTheory.ThK.FlagCT

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def chainEmb {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (k : ℕ) : Matrix (Fin d) (Fin (d₁ - 2 * k)) E :=
  Nat.rec (motive := fun k => Matrix (Fin d) (Fin (d₁ - 2 * k)) E) H'.ι (fun k M => M * (pl k).ι) k

def flagX {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (r : ℕ) :
    Matrix (Fin d) (Fin r) E :=
  Matrix.of fun a k => if k.1 = 0 then H'.x a else (chainEmb H' pl (k.1 - 1) *ᵥ (pl (k.1 - 1)).x) a

def flagY {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (r : ℕ) :
    Matrix (Fin d) (Fin r) E :=
  Matrix.of fun a k => if k.1 = 0 then H'.y a else (chainEmb H' pl (k.1 - 1) *ᵥ (pl (k.1 - 1)).y) a

variable (σ) in

def unipFlag {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) : Subgroup (UA σ W.J) :=
  Subgroup.closure {u | (∃ A : Matrix (Fin (i + 1)) (Fin (i + 1)) (AE F E), A.BlockTriangular id ∧ (∀ k, A k k = 1) ∧
      mat u * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) * A) ∧
    ∀ z, ∃ a : Fin (i + 1) → AE F E,
      mat u *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) = incM F (chainEmb H' pl i) *ᵥ z + incM F (flagX H' pl (i + 1)) *ᵥ a}

def IsCTOn {n : ℕ} {W : Spc F E n} (N : Subgroup (UA σ W.J)) (f c : UA σ W.J → ℂ) : Prop :=
  ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ W.J).subgroupOf N) 𝓕 μ → μ 𝓕 = 1 → ∀ h, c h = ∫ u in 𝓕, f (u.1 * h) ∂μ

def IsLeviFlag {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) {Y : Spc F E (d₁ - 2 * i)} (h₁ : UA σ Y.J) (h : UA σ W.J) : Prop :=
  mat h * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) ∧
    mat h * incM F (flagY H' pl (i + 1)) = incM F (flagY H' pl (i + 1)) ∧
    mat h * incM F (chainEmb H' pl i) = incM F (chainEmb H' pl i) * mat h₁

end GlobalTheory.ThK.FlagCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_of_isCuspForm' : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → GroundTheory.Automorphic.AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | exact GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero | (intros; apply GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowthStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_levi_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y, ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  first | exact @GlobalTheory.SliceTwo.Growth.norm_slice_le | exact GlobalTheory.SliceTwo.Growth.norm_slice_le | (intros; apply GlobalTheory.SliceTwo.Growth.norm_slice_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelic
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.DerCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_isRealLine_finPts {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {k : GAd σ J}
    (hk : k ∈ finPts σ J) : Commute (γ t) k := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  obtain ⟨y, e, -⟩ := hy t
  rw [e]; exact commute_embArch σ J y (mem_finPts_iff_forall.1 hk w)

theorem foldr_lineDer_mul_level {φ : GAd σ J → ℂ} {U : Subgroup (GAd σ J)}
    (hφ : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, l.foldr lineDer φ (g * k) = l.foldr lineDer φ g := by
  intro l
  induction l with
  | nil => intro _ k hk hk' g; exact hφ k hk hk' g
  | cons γ l ih =>
    intro hl k hk hk' g
    have hγ := hl γ List.mem_cons_self
    have ih' := ih (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) k hk hk'
    simp only [List.foldr_cons, lineDer]
    congr 1
    funext t
    rw [mul_assoc, ← (commute_isRealLine_finPts hγ t hk').eq, ← mul_assoc, ih']

theorem eventually_decomp {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (g₀ : GAd σ J) :
    Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝 1) ∧
    ∀ᶠ g in 𝓝 g₀, ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ U ∧ ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ finPts σ J := by
  have hc : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    exact Continuous.tendsto' (by fun_prop) g₀ 1 (by simp)
  have h1 : Tendsto (fun h => ofInf σ J (projInf σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofInf σ J).comp (continuous_projInf σ J)) 1 1 (by simp)
  have h2 : Tendsto (fun h => ofFin σ J (projFin σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofFin σ J).comp (continuous_projFin σ J)) 1 1 (by simp)
  refine ⟨h1.comp hc, ?_⟩
  filter_upwards [(h2.comp hc).eventually (hU.mem_nhds U.one_mem)] with g hg
  exact ⟨hg, mem_finPts.2 (projInf_ofFin σ J _)⟩

theorem chart (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
      ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod :=
  GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints F E σ h n J hJ

theorem continuous_foldr_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  intro F E _ _ _ _ _ σ h n J hJ φ ⟨U, hU, hlev⟩ _ hsm l hl
  obtain ⟨m, η, s, hη, hs, hP⟩ := chart h hJ
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hH : Continuous fun t : Fin m → ℝ => l.foldr lineDer φ (g₀ * (List.ofFn fun i => η i (t i)).prod) :=
    (GlobalTheory.ThK.RealLineGrowthDerivative.contDiff_foldr_lineDer hsm l hl m η hη g₀).continuous
  have hη0 : ∀ i, η i 0 = 1 := fun i => by
    have e := isRealLine_add F E σ h n J (η i) (hη i) 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have h0 : (List.ofFn fun i => η i ((0 : Fin m → ℝ) i)).prod = 1 := by
    simp [hη0]
  obtain ⟨hx, hu⟩ := eventually_decomp hU g₀
  have hx' : Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝[(infPts σ J : Set (GAd σ J))] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun g => mem_infPts.2 (projFin_ofInf σ J _)⟩
  have key : ∀ᶠ g in 𝓝 g₀, l.foldr lineDer φ (g₀ * (List.ofFn fun i =>
      η i (s (ofInf σ J (projInf σ J (g₀⁻¹ * g))) i)).prod) = l.foldr lineDer φ g := by
    filter_upwards [hu, hx'.eventually hP] with g hu' hP'
    rw [← hP']
    have e : g = g₀ * ofInf σ J (projInf σ J (g₀⁻¹ * g)) * ofFin σ J (projFin σ J (g₀⁻¹ * g)) := by
      rw [mul_assoc, ofInf_projInf_mul_ofFin_projFin, mul_inv_cancel_left]
    conv_rhs => rw [e]
    exact (foldr_lineDer_mul_level hlev l hl _ hu'.1 hu'.2 _).symm
  have lim := (hH.tendsto 0).comp (hs.comp hx')
  rw [h0, mul_one] at lim
  exact lim.congr' key

end GlobalTheory.DerCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhiIndep

open ReciprocityTheory.ChartRestriction.G.FD in

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    apply mul_left_cancel₀ (mul_ne_zero (hν g) (bchar_ne_zero (la k) hb))
    rw [mul_zero, Finset.mul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]

set_option maxHeartbeats 1000000 in

theorem phiJ_indep (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (m : ℕ) (b : Fin m → T.R j)
    (hs : ∀ k, b k ∈ sec (T.Q.Xo j) T.Q.c a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun k => T.phiJ j σ a (b k) := by
  obtain ⟨th, hr, -, hD⟩ := h.dictU j hj σ hσ
  have hI := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ a n hd m b hs hb
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along (T.U j σ).X (laU (T.U j σ) a n) (T.dict j σ) hD.2.2.2.2.1 (h.chiTriv j hj σ hσ a n hd)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) ?_
    (fun k => rdU (T.U j σ) (b k)) (fun i k => (h.unf j hj σ hσ).2.2.2.2.1 a n hd _ (hs i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  · intro i g
    simp only [CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

theorem phiC_indep_of (D : D7) (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (b : Fin m → T.R j)
    (H : LinearIndependent ℂ fun k => T.phiJ j σ a (b k)) :
    LinearIndependent ℂ fun k => phiC T hV a (b k) := by
  subst hV
  exact H

set_option maxHeartbeats 1000000 in

theorem phiC_indep : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  intro D T κ h i σ hσ hV m b hb
  refine phiC_indep_of D T hV _ (fun k => (b k : T.R ((i : ℕ) + 1))) ?_
  exact phiJ_indep D T h _ (inR i) σ hσ _ (κ i).n (dom_wtA (κ i)) m _
    (fun k => cusp_le_sec _ _ _ _ _ (b k).2)
    (hb.map' (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype (Submodule.ker_subtype _))

end GlobalTheory.PhiIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariationStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ), (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  first | exact @GlobalTheory.CuspRep.norm_le_of_unip_variation | exact GlobalTheory.CuspRep.norm_le_of_unip_variation | (intros; apply GlobalTheory.CuspRep.norm_le_of_unip_variation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_paired_with_itself : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, GlobalTheory.DiscSpec.IsNormalised π → Paired π π invTOp := by
  first | exact @GlobalTheory.GKPair.paired_invTOp | exact GlobalTheory.GKPair.paired_invTOp | (intros; apply GlobalTheory.GKPair.paired_invTOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  first | exact @GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | exact GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | (intros; apply GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroupStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_rational_points_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)), DiscreteTopology ((ratU σ J).subgroupOf N) := by
  first | exact @GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | exact GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | (intros; apply GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianFormCharPolyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_form_char_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := by
  first | exact @GlobalTheory.EllHermGlobal.exists_charpoly_herm | exact GlobalTheory.EllHermGlobal.exists_charpoly_herm | (intros; apply GlobalTheory.EllHermGlobal.exists_charpoly_herm <;> assumption)
end

