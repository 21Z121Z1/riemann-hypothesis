import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HermitianCoefficientIdentityOne

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EQMulDiagQMulEQMem
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

open Classical in

def eQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if a j ∈ 𝔭 then 1 else 0

def NormOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧ IsUnit P.det

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem eQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (eQ K 𝔭 k a)ᴴ = eQ K 𝔭 k a := by
  unfold eQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem eQ_mul_diagQ_mul_eQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) i j ∈
      (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  unfold eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with hij hi
  · rw [one_mul, mul_one]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) hi)
  · simp
  · exact zero_mem _

theorem solveOnto_of_norm (hN : NormOnto) : SolveOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, hY, hPY, hW, hWh, hEW, hEP1, hEP2, hdet⟩ := hN K F hK 𝔭 h𝔭 m a ha k hk Y
  have hEh := eQ_conjTranspose (K := K) 𝔭 k a
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a

  have h2 : P * eQ K 𝔭 k a = eQ K 𝔭 k a * P := hEP2.trans hEP1.symm
  have h1 : Pᴴ * eQ K 𝔭 k a = eQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose h2
    rw [conjTranspose_mul, conjTranspose_mul, hEh] at h
    exact h.symm
  have hu : IsUnit (Pᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star

  obtain ⟨Z', hZ'⟩ := exists_solve_quot hK h𝔭 (k := k) (by omega)
    (H := eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) (P := P) (Q := (Pᴴ)⁻¹) (S := W)
    (by simp only [conjTranspose_mul, hEh, hH, Matrix.mul_assoc])
    (fun i j => eQ_mul_diagQ_mul_eQ_mem a i j)
    (fun i j => by rw [Matrix.mul_nonsing_inv _ hu, sub_self]; simp)
    hWh
  refine ⟨Y', P, W, eQ K 𝔭 k a * Z' * eQ K 𝔭 k a, Z₀, hY, hPY, hW, ?_⟩
  have h2' : ∀ X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X * P * eQ K 𝔭 k a = X * eQ K 𝔭 k a * P :=
    fun X => by rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have key : W + Pᴴ * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) + (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * P +
      (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) =
      eQ K 𝔭 k a * (W + Pᴴ * Z' + Z'ᴴ * P + Z'ᴴ * (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) * Z') * eQ K 𝔭 k a := by
    simp only [conjTranspose_mul, hEh, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h2',
      ← h1, hEW] <;> abel
  rw [key, hZ', Matrix.mul_zero, Matrix.zero_mul]

theorem discOnto_of_norm (hU : UDModel) (hN : NormOnto) : DiscOnto :=
  discOnto_of_solve hU (solveOnto_of_norm hN)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount
section
namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem glueLoc_of_fibCount (hn : FibCount) : GlueLoc :=
  glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def glueFam (K : Type) {F V : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup V] [Module K V]
    (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (b : Fin n → V) (a : Fin n → 𝓞 F) (π : 𝓞 F) (w : Fin m → V)
    (τ : Fin n → Fin m) : Fin n ⊕ Fin m → V :=
  Sum.elim (fun i => if vF 𝔭 (a i) = 0 then b i else
    ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i))) w

def FamTop : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) = ⊤

def FamGram : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∀ i j, h (glueFam K 𝔭 b a π w τ i) (glueFam K 𝔭 b a π w τ j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

def FamDual : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))) ≤
        locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))

def FamMeet : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

theorem glueAssemble_of (h0 : FamTop) (h1 : FamGram) (h2 : FamDual) (h3 : FamMeet) :
    GlueAssemble := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  refine ⟨locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))),
    ⟨_, isLattice_span _ (h0 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg), rfl⟩,
    le_antisymm (h2 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)
      (le_dualF_of_gram hF h h𝔭.isPrime _ (h1 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)),
    h3 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg⟩

theorem glueLocal_of_fam (hJ : JordanExists) (hV : GlueVecs) (h0 : FamTop) (h1 : FamGram)
    (h2 : FamDual) (h3 : FamMeet) : Formalism.L2.SG.Pf.G7.GlueLocal :=
  glueLocal_of_of hJ hV (glueAssemble_of h0 h1 h2 h3)

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueProdOfIso
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem glueProd_of_iso (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp) :
    GlueProd := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos M hM Λ₀ hΛ₀ T hT
  refine ⟨⟨genus_of_fib h1 h2 h6 hI hK hF hs hnd hUc hpos hM hΛ₀ hT, fun hg 𝔭 h𝔭 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hg h𝔭⟩, card_glue hK hF hUc hM hΛ₀ hT⟩

end Formalism.L2.SG.Pf.G8

namespace Formalism.L2.SG.Pf.Cnt

theorem glueProd_of (h1 : JordanExists) (h2 : JordanInv) (h3 : JordanIsom) (h6 : GlueLoc) : GlueProd :=
  G8.glueProd_of_iso h1 h2 h6 (G8.isomFixOfExp_of h3)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GramComb
section
noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TotPosAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), star x = x → Formalism.MainNotions.S.LocalSplitGroups.TotPos x → Formalism.HermitianLattices.Ext.L3.TotPos x

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_comb' {ι : Type} [Fintype ι] (p : ι → S.V) (A : Matrix ι ι E) (b c : ι) :
    S.hT (∑ a, A a b • p a) (∑ a, A a c • p a) =
      (A.conjTranspose * Matrix.of (fun a a' => S.hT (p a) (p a')) * A) b c := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, starRingEnd_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
    | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)

variable {r : ℕ}

def gv (y : Fin r → S.V) (z : S.V) (N : ℕ) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) y ((-((N : E)⁻¹)) • z)

variable (E) in

def Gam (r N' : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -(N' : E) else 0

def Gam' (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  (Z⁻¹).conjTranspose * Gam E r N' * Z⁻¹

def Psi (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (d : Fin r) (a : Fin (r + 1)) : E :=
  if a = Fin.last r then Gam' N' Z (Fin.castSucc d) (Fin.last r) else Gam' N' Z (Fin.castSucc d) a / 2

def pv (e y : Fin r → S.V) (z : S.V) (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w0 : S.V)
    (a : Fin (r + 1)) : S.V :=
  gv y z N a + ∑ d, Psi N' Z d a • e d + (if a = Fin.last r then (1 : E) else 0) • w0

def tv (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Gam' N' Z (Fin.last r) (Fin.last r) + (N : E)⁻¹

theorem gam_herm (N' : ℕ) (a b : Fin (r + 1)) : star (Gam E r N' a b) = Gam E r N' b a := by
  simp only [Gam, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem gam'_herm (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    star (Gam' N' Z a b) = Gam' N' Z b a := by
  have hG : (Gam E r N').conjTranspose = Gam E r N' := by
    ext a b; rw [Matrix.conjTranspose_apply, gam_herm]
  have h1 : (Gam' N' Z).conjTranspose = Gam' N' Z := by
    simp only [Gam', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  have := congrFun (congrFun h1 b) a
  rwa [Matrix.conjTranspose_apply] at this

variable {e y : Fin r → S.V} {z : S.V} {N : ℕ} (h : Dual e y z N) (hN : 0 < N)
include h hN

theorem hgv_e (a : Fin (r + 1)) (d : Fin r) :
    S.hT (gv y z N a) (e d) = if a = Fin.castSucc d then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last d).ne']
    simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.ez d), smul_zero]
  | cast a =>
    simp only [gv, Fin.snoc_castSucc, Fin.castSucc_inj, h.ye]
    by_cases had : a = d
    · subst had; simp
    · simp [had, Ne.symm had]

theorem he_gv (d : Fin r) (a : Fin (r + 1)) :
    S.hT (e d) (gv y z N a) = if a = Fin.castSucc d then 1 else 0 := by
  rw [hsw, hgv_e h hN]; split_ifs <;> simp

theorem hz_gv (a : Fin (r + 1)) : S.hT z (gv y z N a) = if a = Fin.last r then 1 else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    simp only [gv, Fin.snoc_last, map_smul, smul_eq_mul, h.zz, if_true]
    field_simp
  | cast a =>
    rw [if_neg (Fin.castSucc_lt_last a).ne]
    simp only [gv, Fin.snoc_castSucc]
    exact hsw0 S (h.yz a)

theorem hgv_gv (a a' : Fin (r + 1)) : S.hT (gv y z N a) (gv y z N a') =
    if a = Fin.last r ∧ a' = Fin.last r then -((N : E)⁻¹) else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, h.zz,
        starRingEnd_apply, star_neg, star_inv₀, star_natCast, and_self, if_true]
      field_simp
    | cast a' =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        hsw0 S (h.yz a'), smul_zero]
      simp [(Fin.castSucc_lt_last a').ne]
  | cast a =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, map_smul, h.yz, smul_zero]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast a' =>
      simp only [gv, Fin.snoc_castSucc, h.yy]
      simp [(Fin.castSucc_lt_last a).ne]

variable {N' : ℕ} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {w0 : S.V} (hw : IsW e y z w0)
include hw

theorem hf_pv (a a' : Fin (r + 1)) :
    S.hT (Fin.snoc (α := fun _ => S.V) e z a) (pv e y z N N' Z w0 a') = if a = a' then 1 else 0 := by
  obtain ⟨hwe, -, hwz⟩ := hw
  induction a using Fin.lastCases with
  | last =>
    simp only [pv, Fin.snoc_last, map_add, map_sum, map_smul, smul_eq_mul, hsw0 S (h.ez _), mul_zero,
      Finset.sum_const_zero, add_zero, hwz, hz_gv h hN]
    simp [eq_comm]
  | cast a =>
    simp only [pv, Fin.snoc_castSucc, map_add, map_sum, map_smul, smul_eq_mul, h.ee, mul_zero,
      Finset.sum_const_zero, add_zero, hwe, he_gv h hN]
    simp [eq_comm]

theorem hpv_pv (ht : S.hT w0 w0 = tv N N' Z) (a a' : Fin (r + 1)) :
    S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') = Gam' N' Z a a' := by
  obtain ⟨hwe, hwy, hwz⟩ := hw
  have hgw : ∀ b, S.hT (gv y z N b) w0 = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last => simp [gv, hwz]
    | cast b => simp [gv, hwy]
  have hwg : ∀ b, S.hT w0 (gv y z N b) = 0 := fun b => hsw0 S (hgw b)
  have hwe' : ∀ d, S.hT w0 (e d) = 0 := fun d => hsw0 S (hwe d)
  have key : S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') =
      S.hT (gv y z N a) (gv y z N a') +
      ∑ d, Psi N' Z d a' * S.hT (gv y z N a) (e d) +
      ∑ d, star (Psi N' Z d a) * S.hT (e d) (gv y z N a') +
      star (if a = Fin.last r then (1 : E) else 0) * (if a' = Fin.last r then (1 : E) else 0) * S.hT w0 w0 := by
    simp only [pv, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h.ee, mul_zero, Finset.sum_const_zero, hgw, hwg,
      hwe, hwe', add_zero, zero_add]
    ring
  rw [key, hgv_gv h hN, ht]
  simp only [hgv_e h hN, he_gv h hN, mul_ite, mul_one, mul_zero]
  have hne : ∀ d : Fin r, Fin.last r ≠ Fin.castSucc d := fun d => (Fin.castSucc_lt_last d).ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last => simp [tv, hne]
    | cast a' => simp [hne, Psi, gam'_herm]
  | cast a =>
    induction a' using Fin.lastCases with
    | last => simp [hne, (Fin.castSucc_lt_last a).ne, Psi]
    | cast a' =>
      simp [(Fin.castSucc_lt_last a).ne, (Fin.castSucc_lt_last a').ne, Psi, star_div₀, gam'_herm]

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsAlt
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

private theorem unit_mul_lemma {a c : K} (ha : IsUnitIn S a) (hc : IsUnitIn S c) :
    IsUnitIn S (a * c) :=
  And.intro (mul_ne_zero ha.1 hc.1)
    (And.intro (S.mul_mem ha.2.1 hc.2.1) (by rw [mul_inv]; exact S.mul_mem ha.2.2 hc.2.2))

theorem absorb (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {e : ι → ℕ} {i₀ : ι} (x : ι → K) (hx : ∀ i, x i ∈ S) :
    ∀ T : Finset ι, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : ι → V,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧
      (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _ _ b ho hu
    exact ⟨b, ho, hu, by simp, fun _ _ _ => rfl, rfl, fun _ => Iff.rfl⟩
  · intro a T haT ih hi₀ hlt b ho hu
    have hi₀T : i₀ ∉ T := fun hm => hi₀ (Finset.mem_insert_of_mem hm)
    have hai₀ : i₀ ≠ a := by
      intro h'
      apply hi₀
      rw [h']
      exact Finset.mem_insert_self a T
    obtain ⟨c', ho', hu', hc'0, hc'k, hsp', hiff'⟩ :=
      ih hi₀T (fun j hj => hlt j (Finset.mem_insert_of_mem hj)) b ho hu
    have hc'a : c' a = b a := hc'k a (Ne.symm hai₀) haT
    have hlta : e i₀ < e a := hlt a (Finset.mem_insert_self a T)
    have hu0 : h (c' i₀) (c' i₀) ≠ 0 := unit_ne (hu' i₀)
    have hπ0 : π ≠ 0 := hπ.ne
    obtain ⟨d, hd⟩ : ∃ d, e a = e i₀ + d + 1 := ⟨e a - e i₀ - 1, by omega⟩
    have hs0 : (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹)⁻¹
        * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d) ∈ S :=
      S.mul_mem (hu' i₀).2.2 (S.mul_mem (S.mul_mem (S.mul_mem (hS.star_mem _ (hx a)) (hx a))
        (hu' a).2.1) (S.pow_mem hπ.mem d))
    have hY : IsUnitIn S (h ((1 : K) • c' i₀ + x a • c' a) ((1 : K) • c' i₀ + x a • c' a)
        * (π ^ e i₀)⁻¹) := by
      rw [form_pair (c' i₀) (c' a) (ho' i₀ a hai₀) (ho' a i₀ (Ne.symm hai₀))]
      have eq : (star (1 : K) * 1 * h (c' i₀) (c' i₀) + star (x a) * x a * h (c' a) (c' a))
          * (π ^ e i₀)⁻¹ = (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹) * (1 + π * ((h (c' i₀) (c' i₀)
          * (π ^ e i₀)⁻¹)⁻¹ * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d))) := by
        rw [hd, star_one]
        field_simp
        ring
      rw [eq]
      exact unit_mul_lemma (hu' i₀) (hπ.rad _ hs0)
    obtain ⟨c, ho2, hu2, hc0, hck, hsp2, hiff2⟩ :=
      rot2 hS hπ hs ho' hu' hai₀ hlta.le S.one_mem (hx a) hY
    refine ⟨c, ho2, hu2, ?_, ?_, hsp2.trans hsp', fun v => (hiff2 v).trans (hiff' v)⟩
    · rw [hc0, hc'0, hc'a, one_smul, Finset.sum_insert haT]
      abel
    · intro k hk0 hkT
      have hka : k ≠ a := by
        intro h'
        apply hkT
        rw [h']
        exact Finset.mem_insert_self a T
      have hkT' : k ∉ T := fun h' => hkT (Finset.mem_insert_of_mem h')
      rw [hck k hk0 hka, hc'k k hk0 hkT']

end

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcIdx

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def IndexTypC : Prop :=
  ∀ p : TypX X,
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
      (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
        aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)

end Formalism.L2.SG.Pf.NcIdx
end
end

