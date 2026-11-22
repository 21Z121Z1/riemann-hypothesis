import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

open Polynomial Module

namespace GlobalTheory.Pst.TwistLetters

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {L : FinExt l}
  (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

def smulEnd : (Fin 1 → ↥L.1) →ₗ[ℚ_[l]] End ℚ_[l] V where
  toFun v' := ((LinearMap.lsmul ↥L.1 V) (v' 0)).restrictScalars ℚ_[l]
  map_add' x y := by ext v; simp [add_smul]
  map_smul' c x := by ext v; simp [smul_assoc]

def mulB : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) →ₗ[ℚ_[l]] End ℚ_[l] (V ⊗[ℚ_[l]] Bst P) :=
  TensorProduct.lift ((TensorProduct.mapBilinear (RingHom.id ℚ_[l]) V (Bst P) V (Bst P)).compl₁₂ (smulEnd V)
    (LinearMap.mul ℚ_[l] (Bst P)))

@[simp] theorem mulB_tmul (v' : Fin 1 → ↥L.1) (b' : Bst P) (v : V) (b : Bst P) :
    mulB P V (v' ⊗ₜ b') (v ⊗ₜ b) = (v' 0 • v) ⊗ₜ (b' * b) := by
  simp [mulB, smulEnd]

variable {P V}

theorem mulB_smul (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (a • x) = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_smul_left (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (a • y) x = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', Pi.smul_apply, smul_eq_mul, mul_smul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulV P ↥L.1 V c x) = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_left_comm]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulV_mulB (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) x = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_assoc]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem phiV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    phiV P ↥L.1 V (mulB P V y x) = mulB P V (phiV P ↥L.1 (Fin 1 → ↥L.1) y) (phiV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, phiV_tmul, phiV_tmul, phiV_tmul, mulB_tmul, map_mul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem monV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    monV P ↥L.1 V (mulB P V y x) = mulB P V (monV P ↥L.1 (Fin 1 → ↥L.1) y) x +
      mulB P V y (monV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, monV_tmul, monV_tmul, monV_tmul, mulB_tmul, mulB_tmul, ← TensorProduct.tmul_add]
      congr 1
      simp only [monSt_apply, derivative_mul]
      ring
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

variable {K : FinExt l} (ρs ρt : Representation ↥L.1 ↥(GK K) V)
  (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)

theorem stRep_mulB (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K))
    (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g (mulB P V y x) = mulB P V (stRep P ρm g y) (stRep P ρs g x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, stRep_tmul, stRep_tmul, stRep_tmul, mulB_tmul, map_mul, ht, hm, map_smul, Pi.smul_apply,
        smul_eq_mul, smul_smul, mul_smul]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mem_Dpst (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    {x : V ⊗[ℚ_[l]] Bst P} {y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρs) (hy : y ∈ Dpst P ρm) :
    mulB P V y x ∈ Dpst P ρt := by
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρs).mp hx
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρm).mp hy
  refine (mem_Dpst P ρt).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
  rw [stRep_mulB ρs ρt ρm χ hm ht, h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
    h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]

variable (P)

def dmul (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) :
    ↥(Dpst P ρs) →ₗ[↥L.1] ↥(Dpst P ρm) →ₗ[↥L.1] ↥(Dpst P ρt) :=
  LinearMap.mk₂ ↥L.1 (fun x y => ⟨mulB P V y.1 x.1, mulB_mem_Dpst ρs ρt ρm χ hm ht x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul]))
    (fun x y y' => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul_left]))

variable (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)

@[simp] theorem coe_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    (dmul P ρs ρt ρm χ hm ht x y : V ⊗[ℚ_[l]] Bst P) = mulB P V y.1 x.1 := rfl

theorem dmul_mulD_left (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht (mulD P ρs c x) y = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulB_mulV])

theorem dmul_mulD_right (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht x (mulD P ρm c y) = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulV_mulB])

theorem phiD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    phiD P ρt (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (phiD P ρs x) (phiD P ρm y) :=
  Subtype.ext (by simp [phiV_mulB])

theorem monD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    monD P ρt (dmul P ρs ρt ρm χ hm ht x y) =
      dmul P ρs ρt ρm χ hm ht (monD P ρs x) y + dmul P ρs ρt ρm χ hm ht x (monD P ρm y) :=
  Subtype.ext (by simp [monV_mulB, add_comm])

theorem actD_dmul (g : ↥(GK K)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    actD P ρt g (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (actD P ρs g x) (actD P ρm g y) :=
  Subtype.ext (by simp [stRep_mulB ρs ρt ρm χ hm ht])

end GlobalTheory.Pst.TwistLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.EigTwist

open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def sumL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : Σ m : ℕ, Γ →* GL (Fin m) K :=
  L.foldr (fun p s => ⟨p.1 + s.1, Formalism.MainNotions.SumRepresentations.At.sumRep p.2 s.2⟩) ⟨0, 1⟩

theorem isSSRep_sumL : ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, IsSSRep p.2) →
    IsSSRep (sumL L).2
  | [], _ => GlobalTheory.BCGal.ss_zero _
  | p :: L, h => GlobalTheory.BCGal.ss_sumRep _ _ (h p List.mem_cons_self)
      (isSSRep_sumL L fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem charpoly_sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K).charpoly *
        ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K).charpoly := by
  rw [GlobalTheory.BCGal.sumRep_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem charpoly_sumL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod
  | [], g => by
    rw [List.map_nil, List.prod_nil]
    exact Polynomial.eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; rfl)
  | p :: L, g => by
    rw [List.map_cons, List.prod_cons, ← charpoly_sumL L g]
    exact charpoly_sumRep p.2 (sumL L).2 g

theorem sumRep_mulVec_inl {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (i : Fin a) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inl i)) =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inl)) i := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem sumRep_mulVec_inr {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (j : Fin b) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inr j)) =
      (((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inr)) j := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem eigen_pair (χ : Γ →* Kˣ) {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K)
    (w : Fin (a + b) → K) (hw : w ≠ 0)
    (he : ∀ g, ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) :
    (∃ v : Fin a → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ v = ((χ g : Kˣ) : K) • v) ∨
    (∃ v : Fin b → K, v ≠ 0 ∧ ∀ g, ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ v = ((χ g : Kˣ) : K) • v) := by
  by_cases h1 : w ∘ finSumFinEquiv ∘ Sum.inl = 0
  · right
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inr, fun h2 => hw ?_, fun g => ?_⟩
    · funext j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      rcases s with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    · funext j
      have h3 := congrFun (he g) (finSumFinEquiv (Sum.inr j))
      rw [sumRep_mulVec_inr] at h3
      rw [h3]
      simp
  · left
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inl, h1, fun g => ?_⟩
    funext i
    have h3 := congrFun (he g) (finSumFinEquiv (Sum.inl i))
    rw [sumRep_mulVec_inl] at h3
    rw [h3]
    simp

theorem eigen_sumL (χ : Γ →* Kˣ) : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (w : Fin (sumL L).1 → K),
    w ≠ 0 → (∀ g, (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K) *ᵥ v = ((χ g : Kˣ) : K) • v
  | [], w, hw, _ => (hw (funext fun i => (Nat.not_lt_zero _ i.2).elim)).elim
  | p :: L, w, hw, he => by
    rcases eigen_pair χ p.2 (sumL L).2 w hw he with ⟨v, hv0, hv⟩ | ⟨v, hv0, hv⟩
    · exact ⟨p, List.mem_cons_self, v, hv0, hv⟩
    · obtain ⟨q, hq, u, hu0, hu⟩ := eigen_sumL χ L v hv0 hv
      exact ⟨q, List.mem_cons_of_mem _ hq, u, hu0, hu⟩

theorem eigen_transfer {n m : ℕ} (ρ : Γ →* GL (Fin n) K) (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ)
    (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly)
    (χ : Γ →* Kˣ) (v : Fin n → K) (hv0 : v ≠ 0)
    (hv : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((χ g : Kˣ) : K) • v) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ g, ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ w = ((χ g : Kˣ) : K) • w := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  refine ⟨((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v, fun h0 => hv0 ?_, fun g => ?_⟩
  · have h1 := congrArg (fun u => ((P : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ u) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  · rw [Matrix.mulVec_mulVec, hP g]
    have e : ((P⁻¹ * ρ g * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) * ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]

end GlobalTheory.EigTwist

open GlobalTheory.EigTwist in

theorem GlobalTheory.eigenCharTwist_holds : EigenCharTwist := by
  intro K _ _ Γ _ n ρ L χ hρ hL hc hv
  obtain ⟨v, hv0, hv⟩ := hv
  have hS := isSSRep_sumL L hL
  have hcS : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly :=
    fun g => (hc g).trans (charpoly_sumL L g).symm
  obtain ⟨w, hw0, hw⟩ := eigen_transfer ρ (sumL L).2 hρ hS hcS χ v hv0 hv
  exact eigen_sumL χ L w hw0 hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong

theorem exists_continuous_inv_cLoc {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ ι : GL (Fin n) (w₀.adicCompletion E) → GA E n, Continuous ι ∧ ι 1 = 1 ∧
      ∀ x : UA E n, x ∈ locU n w₀ → ι (cLoc w₀ x) = x.1 := by
  by_cases hsp : IsSplitAt w₀
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w₀ hsp
    refine ⟨fun h => ((e.symm h : locU n w₀) : UA E n).1,
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩
    have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
      rw [← he ⟨x, hx⟩]
      exact e.symm_apply_apply _
    simp only [h1]
  · have hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀ := by
      by_contra hne
      exact hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩
    have hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀ := by
      have h := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀
      change GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h
      rwa [hc0] at h
    refine ⟨fun h => finGL E n (locGL E n w₀ h),
      GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp,
      fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩

theorem exists_algForm_ofType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU E n → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  intro E _ _ _ n lam K U hK hU w₀
  classical
  let π : AutSub E n := ⟨U, hU.aut⟩
  set W := (AU.mk π).wt with hWdef
  have hWat : ∀ τ, W.at τ = lam τ := fun τ => by
    have h1 : (AU.mk π).HasWt τ (lam τ) := (AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)
    exact hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)
  let M := π.finPart W
  have hM0 : M ≠ ⊥ := AutSub.finPart_wt_ne_bot E n π
  have hV : π.V = Pairs.img (Pairs.jOf W M) := Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1
  let b := Module.finBasis ℂ W.Sp
  obtain ⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by
    rw [Pairs.range_total, ← hV]
    exact hφU
  let Fx : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ}
      add_mem' := fun {x y} hx hy k hk => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, hx k hk, hy k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun r ψ h k hk => by
        simp only [Set.mem_setOf_eq] at h ⊢
        rw [map_smul, h k hk] }
  have hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx := fun x u hu k hk => by
    change RU E n k (RU E n x.1 u) = RU E n x.1 u
    rw [RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]
  have hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx := Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1)
    (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    rw [← hc, Pairs.total_apply]
    simp [h]
  have hS : IsOpen {k : finU E n | algRep W k (c a).1 = (c a).1} := isSmooth_algRep W (c a).1
  obtain ⟨ι, hι, hι1, hιx⟩ := exists_continuous_inv_cLoc n w₀
  have hS1 : {k : finU E n | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU E n) :=
    hS.mem_nhds (by
      show algRep W 1 (c a).1 = (c a).1
      rw [map_one]
      rfl)
  rw [nhds_subtype, Filter.mem_comap] at hS1
  obtain ⟨T1, hT1, hT1S⟩ := hS1
  rw [nhds_subtype, Filter.mem_comap] at hT1
  obtain ⟨T, hT, hTT1⟩ := hT1
  refine ⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v,
    fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT),
    fun x hx hxN v g => ?_⟩
  have hxfin : x ∈ finU E n := (Subgroup.mem_inf.1 hx).1
  have h2 : x.1 ∈ T := hιx x hx ▸ hxN
  have hk : (⟨x, hxfin⟩ : finU E n) ∈ {k : finU E n | algRep W k (c a).1 = (c a).1} := hT1S (hTT1 h2)
  exact congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g

end GlobalTheory.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  first | exact @GlobalTheory.EmbExt.main | exact GlobalTheory.EmbExt.main | (intros; apply GlobalTheory.EmbExt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHostStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_ladicGalRep_model_finite_ext_host : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  first | exact @GlobalTheory.CompactRepField.exists_continuous_model | exact GlobalTheory.CompactRepField.exists_continuous_model | (intros; apply GlobalTheory.CompactRepField.exists_continuous_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  first | exact @GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | exact GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | (intros; apply GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeper_congruence_conj_into_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  first | exact @GlobalTheory.ConjCong.exists_cong_conj | exact GlobalTheory.ConjCong.exists_cong_conj | (intros; apply GlobalTheory.ConjCong.exists_cong_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivialStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_parInd_of_jacquet_nontrivial : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  first | exact @GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial | exact GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial | (intros; apply GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → GlobalTheory.SplitWeil.IsTame μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = (μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))⁻¹) → ∀ u : W, u ≠ 0 → (∀ g h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → h.val = (g⁻¹).val.transpose → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom h) u = ((ξ d : ℂˣ) : ℂ) • u) → ∃ u' : W, u' ≠ 0 ∧ GlobalTheory.ThetaGL.IsParahoricVec μ π u' := by
  first | exact @GlobalTheory.ConjParahoric.exists_parahoricVec | exact GlobalTheory.ConjParahoric.exists_parahoricVec | (intros; apply GlobalTheory.ConjParahoric.exists_parahoricVec <;> assumption)
end

