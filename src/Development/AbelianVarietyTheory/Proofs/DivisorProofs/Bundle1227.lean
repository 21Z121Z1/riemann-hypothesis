import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothFiniteTypeSubalgebraInRingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (S : Finset κ'),
    (∀ x ∈ S, x ∈ F.ring) → ∃ A : Subalgebra ℂ κ', Algebra.Smooth ℂ A ∧
      A.toSubring ≤ F.ring.toSubring ∧ (∀ x ∈ S, x ∈ A) ∧
      ∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.Place.exists_smooth_subalgebra | exact GlobalTheory.FieldPair.Place.exists_smooth_subalgebra | (intros; apply GlobalTheory.FieldPair.Place.exists_smooth_subalgebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_in_image_of_fractionField : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  first | exact @GlobalTheory.GraphLocal.exists_trBasis_lift | exact GlobalTheory.GraphLocal.exists_trBasis_lift | (intros; apply GlobalTheory.GraphLocal.exists_trBasis_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPointStatement
section
open GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  first | exact @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | exact GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel | (intros; apply GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwTraceForm

theorem phi_transpose (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ = (-1 : L) ^ (a - 1) • GlobalTheory.Tw.Phi a L :=
  (GlobalTheory.antidiag_twisted_norm L (RingEquiv.refl L) (fun _ => rfl) a (GlobalTheory.Tw.Phi a L) (by
    ext i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    have : ((i : ℕ) + (j : ℕ) + 1 = a) ↔ j = i.rev := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    simp only [this])).1

theorem phi_map (a : ℕ) (L : Type) [Field L] (c : L →+* L) :
    (GlobalTheory.Tw.Phi a L).map c = GlobalTheory.Tw.Phi a L := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_transpose_mul (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.CuspRep.Phi_mul_transpose a L)

theorem gram_eq (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ⁻¹ : GL (Fin a) L).val)ᵀ * GlobalTheory.Tw.Phi a L := by
  have h : (δ.val * GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹ : GL (Fin a) L).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (δ⁻¹ : GL (Fin a) L).val, Units.inv_mul, Matrix.one_mul,
      phi_transpose_mul]
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_transpose (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * (δ.val * GlobalTheory.Tw.Phi a L)ᵀ = 1 := by
  rw [gram_eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.Tw.Phi a L),
    GlobalTheory.CuspRep.Phi_mul_transpose, Matrix.one_mul, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one]

theorem gram_norm (a : ℕ) (L : Type) [Field L] (c : L →+* L) (δ : GL (Fin a) L) :
    (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ)ᵀ * (δ * thetaGL a c δ).val
      = (-1 : L) ^ (a - 1) • (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ).map c := by
  have hθ : (thetaGL a c δ).val
      = GlobalTheory.Tw.Phi a L * (((δ⁻¹ : GL (Fin a) L).val).map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  rw [gram_eq, Units.val_mul, hθ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map, phi_map]
  set Φ := GlobalTheory.Tw.Phi a L
  set Di := (δ⁻¹ : GL (Fin a) L).val
  set X := (Di.map c)ᵀ
  calc Φᵀ * Di * (δ.val * (Φ * X * Φᵀ))
      = Φᵀ * (Di * δ.val) * Φ * X * Φᵀ := by
        simp only [Matrix.mul_assoc]
    _ = X * Φᵀ := by
        rw [Units.inv_mul, Matrix.mul_one, phi_transpose_mul, Matrix.one_mul]
    _ = (-1 : L) ^ (a - 1) • (X * Φ) := by
        rw [phi_transpose, Matrix.mul_smul]

theorem form_asym {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (S N : Matrix n n k) (ε : k) (h : S.map σ = ε • (Sᵀ * N))
    (u v : n → k) :
    σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (ε • N *ᵥ u) ⬝ᵥ S *ᵥ (fun j => σ (v j)) := by
  have h1 : σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (fun j => σ (v j)) ⬝ᵥ S.map σ *ᵥ u := by
    rw [show σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (σ : k →+* k) (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) from rfl,
      RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext j
    simp [hσ]
  rw [h1, h, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, smul_dotProduct, dotProduct_comm, smul_eq_mul]

end GlobalTheory.TwTraceForm

namespace GlobalTheory.TwTraceForm

theorem exists_trace_form : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  intro K B L _ e c hec hcc hg a Q hBP hQs hQd δ hδ
  classical
  let f : L →+* K.E := e.symm.toRingHom
  have hf : ∀ x, f (c x) = K.c (f x) := by
    intro x
    apply e.injective
    show e (e.symm (c x)) = e (K.c (e.symm x))
    rw [hec, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  set G := ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ with hG
  set N := (δ * thetaGL a c δ).val with hN
  set S := G.map f with hS
  set N' := N.map f with hN'
  set ε : K.E := (-1) ^ (a - 1) with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hkey : Sᵀ * N' = ε • S.map K.c := by
    have h0 := congrArg f.mapMatrix (gram_norm a L c δ)
    rw [map_mul] at h0
    simp only [RingHom.mapMatrix_apply] at h0
    rw [Matrix.transpose_map] at h0
    change Sᵀ * N' = _ at h0
    rw [h0]
    ext i j
    simp [f, hf, hε, Matrix.map_apply, Matrix.smul_apply]
    exact hf _
  have hSc : S.map K.c = ε • (Sᵀ * N') := by rw [hkey, smul_smul, hεε, one_smul]
  set Y := ((δ.val * GlobalTheory.Tw.Phi a L)ᵀ).map f with hY
  have hSY : S * Y = 1 := by
    have h0 := congrArg f.mapMatrix (gram_mul_transpose a L δ)
    rw [map_mul, map_one] at h0
    exact h0
  have hsep : (LinearMap.mulLeft K.E B.g).charpoly.Separable := by
    show B.P.Separable
    rw [hBP]; exact hQs.map
  have hchar : (LinearMap.mulLeft K.E B.g).charpoly = (Matrix.toLin' N').charpoly := by
    rw [Matrix.charpoly_toLin', hN', Matrix.charpoly_map, hδ]
    exact hBP
  obtain ⟨ψ, hψ⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K.E B.A (Fin a → K.E)
    (LinearMap.mulLeft K.E B.g) (Matrix.toLin' N') hsep hchar
  have hψ' : ∀ y, ψ (B.g * y) = N' *ᵥ ψ y := fun y => by simpa using hψ y
  have hc1 : ∀ j : Fin a, (fun k => K.c ((Pi.single j (1 : K.E) : Fin a → K.E) k)) = (Pi.single j 1 : Fin a → K.E) := by
    intro j
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let s : B.A → B.A → K.E := fun y z => ψ y ⬝ᵥ S *ᵥ (fun j => K.c (ψ z j))
  have hadd : ∀ x y z, s (x + y) z = s x z + s y z := by
    intro x y z
    simp only [s, map_add, add_dotProduct]
  have hlin : ∀ (r : K.E) x z, s (r • x) z = r * s x z := by
    intro r x z
    simp only [s, map_smul, smul_dotProduct, smul_eq_mul]
  have hnd : ∀ y, (∀ z, s y z = 0) → y = 0 := by
    intro y hy
    have hv : ψ y ᵥ* S = 0 := by
      funext j
      have h1 := hy (ψ.symm (Pi.single j 1))
      simp only [s, LinearEquiv.apply_symm_apply] at h1
      rw [hc1 j, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    have h2 : ψ y = 0 := by
      rw [← Matrix.vecMul_one (ψ y), ← hSY, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
    exact ψ.injective (by rw [h2, map_zero])
  have hsym : ∀ y z, K.c (s z y) = s ((-1 : B.A) ^ (a - 1) * B.g * y) z := by
    intro y z
    have hψε : ψ ((-1 : B.A) ^ (a - 1) * B.g * y) = ε • N' *ᵥ ψ y := by
      have h1 : (-1 : B.A) ^ (a - 1) = algebraMap K.E B.A ε := by simp [hε]
      rw [h1, mul_assoc, ← Algebra.smul_def, map_smul, hψ']
    simp only [s]
    rw [hψε]
    exact form_asym K.c K.c_c S N' ε hSc (ψ y) (ψ z)
  obtain ⟨β, hβ, hs⟩ := (GlobalTheory.SesqAsym.sesq_asym K B hg hsep ((-1) ^ (a - 1))
    (neg_one_pow_eq_or B.A (a - 1))).2 s hadd hlin hnd hsym
  refine ⟨β, hβ, (Pi.basisFun K.E (Fin a)).map ψ.symm, ?_⟩
  ext i j
  simp only [Matrix.of_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  rw [← hs]
  simp only [s, LinearEquiv.apply_symm_apply]
  rw [hc1 j, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hS, Matrix.map_apply]
  exact (e.apply_symm_apply _).symm

end GlobalTheory.TwTraceForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfUnitaryGeneratorInvariantForm
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}

def sv (G : Matrix (Fin m) (Fin m) K.E) (x y : Fin m → K.E) : K.E :=
  x ⬝ᵥ (G *ᵥ fun j => K.c (y j))

def sf (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E) (a z : B.A) : K.E :=
  sv G (b.repr a) (b.repr z)

variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sf_add_left (a a' z : B.A) : sf b G (a + a') z = sf b G a z + sf b G a' z := by
  simp [sf, sv, map_add, add_dotProduct]

theorem sf_smul_left (l : K.E) (a z : B.A) : sf b G (l • a) z = l * sf b G a z := by
  simp [sf, sv, map_smul, smul_dotProduct]

theorem sf_add_right (a z z' : B.A) : sf b G a (z + z') = sf b G a z + sf b G a z' := by
  have : (fun j => K.c ((b.repr (z + z')) j)) = (fun j => K.c (b.repr z j)) + fun j => K.c (b.repr z' j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_add, dotProduct_add]

theorem sf_smul_right (l : K.E) (a z : B.A) : sf b G a (l • z) = K.c l * sf b G a z := by
  have : (fun j => K.c ((b.repr (l • z)) j)) = K.c l • fun j => K.c (b.repr z j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sf_basis (i j : Fin m) : sf b G (b i) (b j) = G i j := by
  simp [sf, sv, dotProduct, mulVec, Finsupp.single_apply, Pi.single_apply]

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sv_inv (N : Matrix (Fin m) (Fin m) K.E) (hN : Nᵀ * G * N.map K.c = G) (x y : Fin m → K.E) :
    sv G (N *ᵥ x) (N *ᵥ y) = sv G x y := by
  have hc : (fun j => K.c ((N *ᵥ y) j)) = N.map K.c *ᵥ fun j => K.c (y j) := by
    ext j; exact RingHom.map_mulVec (K.c : K.E →+* K.E) N y j
  unfold sv
  rw [hc, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hN]

theorem sf_mul_u (u : B.A) (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (a z : B.A) :
    sf b G (u * a) (u * z) = sf b G a z := by
  unfold sf
  have h1 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) a
  have h2 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) z
  simp only [LinearMap.mulLeft_apply] at h1 h2
  rw [← h1, ← h2, sv_inv G _ hN]

theorem sf_adj (u : B.A) (hu : Algebra.adjoin K.E {u} = ⊤) (hu1 : u * B.σ u = 1)
    (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (x a z : B.A) :
    sf b G (x * a) z = sf b G a (B.σ x * z) := by
  have hx : x ∈ Algebra.adjoin K.E {u} := hu ▸ Algebra.mem_top
  revert a z
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    intro a z
    conv_lhs => rw [show z = x * (B.σ x * z) by rw [← mul_assoc, hu1, one_mul]]
    exact sf_mul_u b G x hN a _
  | algebraMap l =>
    intro a z
    rw [← Algebra.smul_def, sf_smul_left, B.σ_alg, ← Algebra.smul_def, sf_smul_right, K.c_c]
  | add x y _ _ hx hy =>
    intro a z
    rw [add_mul, sf_add_left, hx, hy, map_add, add_mul, sf_add_right]
  | mul x y _ _ hx hy =>
    intro a z
    rw [mul_comm x y, mul_assoc, hy, hx, map_mul]; congr 1; ring

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

theorem exists_beta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u : B.A), Algebra.adjoin K.E {u} = ⊤ → u * B.σ u = 1 → (Algebra.traceForm K.E B.A).Nondegenerate → ∀ G : Matrix (Fin m) (Fin m) (w.adicCompletion E), (GlobalTheory.TwLat.mulMat e b u)ᵀ * G * (cj w).mapMatrix (GlobalTheory.TwLat.mulMat e b u) = G → ∃ β : B.A, GlobalTheory.TwLat.gram e b β = G := by
  intro E _ _ _ w K e he B m b u hu hu1 hnd G hG
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft K.E u) with hNdef
  set G' : Matrix (Fin m) (Fin m) K.E := G.map e.symm with hG'
  have hGG : G = G'.map e := by ext i j; simp [hG']
  have hN : Nᵀ * G' * N.map K.c = G' := by
    have h2 : ((Nᵀ * G' * N.map K.c).map e) = G'.map e := by
      rw [← hGG]
      conv_rhs => rw [← hG]
      rw [hGG]
      have : (Nᵀ * G' * N.map K.c).map e = ((e : K.E →+* w.adicCompletion E).mapMatrix) (Nᵀ * G' * N.map K.c) := rfl
      rw [this, map_mul, map_mul]
      congr 1
      ext i j
      simp [GlobalTheory.TwLat.mulMat, hNdef, RingHom.mapMatrix_apply, he]
    exact Matrix.map_injective e.injective h2
  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun a => sf b G' a 1
      map_add' := fun a a' => sf_add_left b G' a a' 1
      map_smul' := fun l a => sf_smul_left b G' l a 1 }
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm ℓ, ?_⟩
  refine Matrix.ext fun i j => ?_
  set β := (LinearMap.BilinForm.toDual _ hnd).symm ℓ
  have hβ : ∀ a, Algebra.trace K.E B.A (β * a) = ℓ a := by
    intro a
    rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  simp only [GlobalTheory.TwLat.gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm]
  rw [mul_assoc, hβ]
  show e (sf b G' (b i * B.σ (b j)) 1) = G i j
  rw [mul_comm, sf_adj b G' u hu hu1 hN, B.σ_σ, mul_one, sf_basis, hG']
  simp

end GlobalTheory.TwLat.BetaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  first | exact @GlobalTheory.exists_weightedMonomialPlace | exact GlobalTheory.exists_weightedMonomialPlace | (intros; apply GlobalTheory.exists_weightedMonomialPlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilated
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ExtKill

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [exp_smul_conj hP]

theorem smoothVec_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem kill_and_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ v : M.Vec, IsExtVec M v → ∀ (ρ : D.what₂.Tau) (p : ℕ) (s : Bool), (∀ a : Fin V.rank, M.ε ρ a = if (a : ℕ) < p then s else !s) → (∀ a b, KillPair (M.ε ρ) a b → RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧ ∀ (t : Fin V.rank → ℝ) (g : GA D V), T v (g * atTau θ V ρ ((M.fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I)) * M.fr ρ)) = Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) * T v g := by
  intro D θ V S M J χ T hθ hT v hv ρ p s hε
  have hP := M.fr_unit ρ
  have hG := M.fr_gram ρ
  obtain ⟨-, hlow, hwt⟩ := hv ρ
  have hlow' : (v ρ : M.H ρ) ∈ lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
  refine ⟨fun a b hab => ?_, fun t g => ?_⟩
  · obtain ⟨hs, hd⟩ := GlobalTheory.T.right_derivative_multiplicity_map_value_eq D θ V S M J χ T hθ hT v ρ
    have hs' := smoothVec_conj (σ := M.σ ρ) hP hG hs
    set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
    obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
    have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
    unfold RderC
    generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
    obtain ⟨u, hu, eu⟩ := hd X hX
    obtain ⟨u', hu', eu'⟩ := hd Y hY
    have hX' := lie_conj hP hG hX
    have hY' := lie_conj hP hG hY
    have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) = Matrix.single a b 1 := by
      rw [← conj_cancel hP (Matrix.single a b 1), ← hZ, ← hXY]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
        Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
      rcases hab with h | h | h
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
      · exact GlobalTheory.T.extremal_lowestKType_killed_compact_roots _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
      · exact GlobalTheory.T.lowestKType_killed_by_negative_noncompact_roots _ _ _ _ _ p s hε (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
    have h0 : u + Complex.I • u' = 0 := by
      apply Subtype.ext
      show (u : M.H ρ) + Complex.I • (u' : M.H ρ) = 0
      rw [hu, hu', ← key, ← dRep_conj hP, ← dRep_conj hP]
      rfl
    rw [eu, eu', ← T.map_update_smul, ← T.map_update_add, h0, T.map_update_zero]
  · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) t
    have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hP hG (kset_uj hK)
    have h := hT.equiv ρ _ hg v (Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) • v ρ) (by
      unfold DSModel.rep
      rw [conj_cancel hP, hwt t hK]
      rfl)
    rw [T.map_update_smul, Function.update_eq_self] at h
    exact (congrFun h g).symm

end GlobalTheory.HolRead.ExtKill
end

