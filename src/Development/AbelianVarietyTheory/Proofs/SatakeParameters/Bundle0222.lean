import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalMemLocalUnitaryGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertLocUnitary

open TensorProduct

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : ReciprocityTheory.Aut.AL L) :
    ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (ReciprocityTheory.Aut.compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [ReciprocityTheory.Aut.compAt, ReciprocityTheory.Aut.conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem loc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set ψ : ReciprocityTheory.Aut.AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (ReciprocityTheory.Aut.compAt L v) with hψ
  have hcomm : ∀ a, Dv.σw (ψ a) = ψ (ReciprocityTheory.Aut.conjAL L a) := by
    intro a
    simp only [hψ, RingHom.comp_apply, RingHom.coe_coe]
    rw [compAt_conjAL, Dv.comm]
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (x.1 : GL (Fin n) (ReciprocityTheory.Aut.AL L)).val with hM
  have hx : M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 := x.2
  set X : Matrix (Fin n) (Fin n) (w.adicCompletion L) := M.map ψ with hX
  have hXval : ((Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) (x : GL (Fin n) (ReciprocityTheory.Aut.AL L))) :
        GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = X := by
    ext i j; rfl
  have hcTX : Formalism.UG.cT Dv.σw X = (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map ψ := by
    ext i j
    simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, hX, hcomm]
  have hXX : X * Formalism.UG.cT Dv.σw X = 1 := by
    rw [hcTX, hX, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hXX' : Formalism.UG.cT Dv.σw X * X = 1 := mul_eq_one_comm.mp hXX
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : GL (Fin n) (w.adicCompletion L)).val with hP
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)).val with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ : Formalism.UG.cT Dv.σw P * P = Formalism.UG.antiJ (w.adicCompletion L) n := Dv.Panti
  show Formalism.UG.cT Dv.σw (((Dv.loc x : GL (Fin n) _)) : Matrix _ _ _) * Formalism.UG.antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) _) : Matrix _ _ _) = Formalism.UG.antiJ (w.adicCompletion L) n
  have hloc : ((Dv.loc x : GL (Fin n) _) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Q * X * P := by
    simp only [InertDatum.loc, Units.val_mul, hXval, hQ, hP]
  have cQP : Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  rw [hloc, ← hJ, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw X * (Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P) * (P * Q) * X * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by
        rw [cQP, hPQ, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Formalism.UG.cT Dv.σw X), hXX', Matrix.one_mul]

end GlobalTheory.InertLocUnitary

theorem GlobalTheory.InertLocUnitary.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n :=
  fun L _ _ _ n v w Dv x => GlobalTheory.InertLocUnitary.loc_mem_GU L n v w Dv x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdSubquot

theorem subquot_dichotomy : ∀ (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q] (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A) (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ), τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ → IsSubquotient τ α ∨ IsSubquotient τ κ := GlobalTheory.T.isSubquotient_of_exact_middle_irreducible

theorem exists_irreducible_of_pred : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := GlobalTheory.T.property_descends_finiteLength_to_irreducible_subquotient

theorem parIndMap_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := GlobalTheory.T.parabolicInduction_preserves_injective_and_exactness

def extMapLeft {G H A B W : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup W] [Module ℂ W] {α : Representation ℂ G A} {β : Representation ℂ G B}
    (i : α.IntertwiningMap β) (ρ : Representation ℂ H W) :
    (extTensor α ρ).IntertwiningMap (extTensor β ρ) where
  toLinearMap := i.toLinearMap.rTensor W
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

def extMapRight {G H A B X : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) {α : Representation ℂ H A} {β : Representation ℂ H B}
    (i : α.IntertwiningMap β) :
    (extTensor ρ α).IntertwiningMap (extTensor ρ β) where
  toLinearMap := i.toLinearMap.lTensor X
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

theorem prod₂_exact_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A B W : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] (α : Representation ℂ (GL (Fin r) k) A) (β : Representation ℂ (GL (Fin r) k) B) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ α ρ₂).IntertwiningMap (prod₂ β ρ₂), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin r) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ β ρ₂).IntertwiningMap (prod₂ γ ρ₂), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t A B W _ _ _ _ _ _ α β ρ₂ i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapLeft i ρ₂) s) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapLeft i ρ₂) s) hi'
  refine ⟨parIndMap _ (compMap (extMapLeft i ρ₂) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapLeft q ρ₂) s), hex _ _ (compMap (extMapLeft q ρ₂) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.rTensor W) (q.toLinearMap.rTensor W) := by
    refine rTensor_exact W ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem prod₂_exact_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (X A B : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρ₁ : Representation ℂ (GL (Fin r) k) X) (α : Representation ℂ (GL (Fin t) k) A) (β : Representation ℂ (GL (Fin t) k) B) (i : α.IntertwiningMap β), Function.Injective i → ∃ I : (prod₂ ρ₁ α).IntertwiningMap (prod₂ ρ₁ β), Function.Injective I ∧ ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ (GL (Fin t) k) C) (q : β.IntertwiningMap γ), Function.Surjective q → (∀ a, q (i a) = 0) → (∀ b, q b = 0 → ∃ a, i a = b) → ∃ Q : (prod₂ ρ₁ β).IntertwiningMap (prod₂ ρ₁ γ), ∀ φ, Q φ = 0 → ∃ ψ, I ψ = φ := by
  intro k _ _ _ _ r t X A B _ _ _ _ _ _ ρ₁ α β i hi
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extMapRight ρ₁ i) s) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hi
  obtain ⟨hI, hex⟩ := parIndMap_exact k Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    _ _ (compMap (extMapRight ρ₁ i) s) hi'
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ i) s), hI, fun C _ _ γ q hq hqi hiq => ?_⟩
  refine ⟨parIndMap _ (compMap (extMapRight ρ₁ q) s), hex _ _ (compMap (extMapRight ρ₁ q) s) ?_⟩
  have hE : Function.Exact (i.toLinearMap.lTensor X) (q.toLinearMap.lTensor X) := by
    refine lTensor_exact X ?_ hq
    intro b
    refine ⟨hiq b, ?_⟩
    rintro ⟨a, rfl⟩
    exact hqi a
  intro y hy
  exact (hE y).1 hy

theorem nontrivial_of_prod₂ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ₁ : Representation ℂ (GL (Fin r) k) X) (σ₂ : Representation ℂ (GL (Fin t) k) Y)
    (h : IsSubquotient π.π (prod₂ σ₁ σ₂)) : Nontrivial X ∧ Nontrivial Y := by
  obtain ⟨S, f, hf⟩ := h
  have := nontrivial_of_irreducible π.irr
  obtain ⟨w, hw⟩ := exists_ne (0 : π.V)
  obtain ⟨φ, rfl⟩ := hf w
  by_contra hc
  rw [not_and_or, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton] at hc
  have hsub : Subsingleton (TensorProduct ℂ X Y) := by
    rcases hc with hc | hc
    · haveI := hc; infer_instance
    · haveI := hc; infer_instance
  apply hw
  have h0 : φ = 0 := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext g
    exact Subsingleton.elim _ _
  rw [h0, map_zero]

theorem step_left {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₁ : HasFiniteLength ρ₁) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin r) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₁ ∧ IsSubquotient π.π (prod₂ σ ρ₂) := by
  refine exists_irreducible_of_pred (GL (Fin r) k) V ρ₁
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ σ ρ₂)) hf₁ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_left k r t Y Y' W σ σ' ρ₂ f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π σ ρ₂ h).1
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_left k r t B.toSubmodule A.toSubmodule W B.toRepresentation
      A.toRepresentation ρ₂ i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem step_right {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ} (π : Irr k (r + t)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W)
    (hf₂ : HasFiniteLength ρ₂) (hπ : IsSubquotient π.π (prod₂ ρ₁ ρ₂)) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ (GL (Fin t) k) Y),
      σ.IsIrreducible ∧ IsSubquotient σ ρ₂ ∧ IsSubquotient π.π (prod₂ ρ₁ σ) := by
  refine exists_irreducible_of_pred (GL (Fin t) k) W ρ₂
    (fun Y _ _ σ => IsSubquotient π.π (prod₂ ρ₁ σ)) hf₂ ?_ ?_ ?_ hπ
  · intro Y Y' _ _ _ _ σ σ' f hf h
    obtain ⟨I, hI, -⟩ := prod₂_exact_right k r t V Y Y' ρ₁ σ σ' f hf
    exact h.trans (IsSubquotient.of_injective I hI)
  · intro Y _ _ σ h
    exact (nontrivial_of_prod₂ π ρ₁ σ h).2
  · intro A B hBA h
    let i : B.toRepresentation.IntertwiningMap A.toRepresentation :=
      ⟨Submodule.inclusion hBA, fun _ => rfl⟩
    let q : A.toRepresentation.IntertwiningMap (subQuot A B) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    obtain ⟨I, hI, hQ⟩ := prod₂_exact_right k r t V B.toSubmodule A.toSubmodule ρ₁ B.toRepresentation
      A.toRepresentation i (Submodule.inclusion_injective hBA)
    obtain ⟨Q, hQ'⟩ := hQ _ (subQuot A B) q (Submodule.Quotient.mk_surjective _)
      (fun a => (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).2 a.2) (by
      intro b hb
      exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero (B.toSubmodule.comap A.toSubmodule.subtype)).1 hb⟩,
        Subtype.ext rfl⟩)
    exact subquot_dichotomy _ _ _ _ _ π.π _ _ _ I Q π.irr hQ' h

theorem irreducible_subquotient_prod₂ : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (π : Irr k (r + t)), IsSmooth ρ₁ → IsSmooth ρ₂ → HasFiniteLength ρ₁ → HasFiniteLength ρ₂ → IsSubquotient π.π (prod₂ ρ₁ ρ₂) → ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSubquotient π₁.π ρ₁ ∧ IsSubquotient π₂.π ρ₂ ∧ IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro _hBZ k _ _ _ _ r t V W _ _ _ _ ρ₁ ρ₂ π h₁ h₂ hf₁ hf₂ hπ
  obtain ⟨Y₁, _, _, σ₁, hσ₁, hsq₁, hP₁⟩ := step_left π ρ₁ ρ₂ hf₁ hπ
  obtain ⟨Y₂, _, _, σ₂, hσ₂, hsq₂, hP₂⟩ := step_right π σ₁ ρ₂ hf₂ hP₁
  exact ⟨{ V := Y₁, π := σ₁, smooth := hsq₁.isSmooth h₁, irr := hσ₁ },
    { V := Y₂, π := σ₂, smooth := hsq₂.isSmooth h₂, irr := hσ₂ }, hsq₁, hsq₂, hP₂⟩

end GlobalTheory.ProdSubquot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.RegAlgCharAlg

theorem expo_mul' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ χ' : HChar E) (τ : E →+* ℂ) :
    expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (τ : E →+* ℂ) :
    expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul' χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isAlgPos_of_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ →
      ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ a ha π χ hreg hpol
  refine GlobalTheory.T.heckeChar_realSubfield_algebraic_of_comp_norm_integral E χ fun τ => ?_
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ
  have h1 := (hm τ).twist ψ⁻¹
  have key := GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (NumberField.ComplexEmbedding.conjugate τ))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
  obtain ⟨n, hn⟩ := (hreg τ).2 z hz
  have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) := by
    rw [key, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
  refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
  rw [expo_inv'] at hn'
  push_cast
  linear_combination hn' + hn

end GlobalTheory.RegAlgCharAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplitStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTheta_relation_of_indicator_relation_split : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  first | exact @GlobalTheory.KerRel.kerTh_relation_of_indicator | exact GlobalTheory.KerRel.kerTh_relation_of_indicator | (intros; apply GlobalTheory.KerRel.kerTh_relation_of_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_rep_parabolic_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first | exact @GlobalTheory.EigenFactor.exists_eig_factor | exact GlobalTheory.EigenFactor.exists_eig_factor | (intros; apply GlobalTheory.EigenFactor.exists_eig_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_bound_place_over_second_embedding : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  first | exact @GlobalTheory.TwU.LowF.lowAt_F | exact GlobalTheory.TwU.LowF.lowAt_F | (intros; apply GlobalTheory.TwU.LowF.lowAt_F <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SysE

set_option maxHeartbeats 1000000 in

theorem matched_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF t P hg cX c0 hM hX hXo
  have gd := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg0 : Good R A.μ0 P := (gd.2.1 t P hg).2.2
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have injX : Function.Injective (R.HX t).e := (hC.models.HX t).1

  have part1 : ∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro h hh y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg0 c0 (R.Th t y)).symm
  refine ⟨part1, ?_⟩
  intro c w hw
  have h01 := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F hC hS SF hSF
  rcases h01 with ⟨h0, h0o, h0n, -, h0e, -⟩
  have hX01 := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX0, hX0o, hX0n⟩
  have eqX : hX P cX = hX0 P cX := by
    ext x
    apply injX
    exact (hXo P hg cX x).trans (hX0o P hg cX x).symm
  have eX : LinearMap.adjoint (hX0 P cX) = hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hX0n.2 P hg cX
  have cX' : Commute (hX0 P cX) (hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hX0n.1 P P hg hg _ _
  have nX0 : Commute (hX0 P cX) (LinearMap.adjoint (hX0 P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX0 P cX) B) _ _ eX.symm cX'
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute B (LinearMap.adjoint B)) _ _ eqX.symm nX0
  have eE : LinearMap.adjoint (h0 P c0) = h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := h0n.2 P hg0 c0
  have cE : Commute (h0 P c0) (h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := h0n.1 P P hg0 hg0 _ _
  have nE : Commute (h0 P c0) (LinearMap.adjoint (h0 P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h0 P c0) B) _ _ eE.symm cE
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h0 P c0)
    (fun _ u => part1 h0 h0o u) (fun _ => nX) (fun _ => nE) () _ w (h0e c P hg0 c0 w hw)

end GlobalTheory.Hk3.SysE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedParabolicInduction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  first | exact @GlobalTheory.SmGL.Relabel.parInd_reindex | exact GlobalTheory.SmGL.Relabel.parInd_reindex | (intros; apply GlobalTheory.SmGL.Relabel.parInd_reindex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V), IsSmooth π → ∀ (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin t), Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  first | exact @GlobalTheory.ProdReorder.ind₂_unit_left | exact GlobalTheory.ProdReorder.ind₂_unit_left | (intros; apply GlobalTheory.ProdReorder.ind₂_unit_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem units_zpow_bilin_comm {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (B : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (u₁ : (Module.End R M₁)ˣ) (u₂ : (Module.End R M₂)ˣ) (u₃ : (Module.End R M₃)ˣ)
    (h : ∀ x y, (u₃ : Module.End R M₃) (B x y) = B ((u₁ : Module.End R M₁) x) ((u₂ : Module.End R M₂) y))
    (n : ℤ) (x : M₁) (y : M₂) :
    ((u₃ ^ n : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁ ^ n : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂ ^ n : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
  have hinv : ∀ x y, ((u₃⁻¹ : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
    intro x y
    have e₁ := LinearMap.congr_fun (Units.mul_inv u₁) x
    have e₂ := LinearMap.congr_fun (Units.mul_inv u₂) y
    rw [Module.End.mul_apply, Module.End.one_apply] at e₁ e₂
    conv_lhs => rw [← e₁, ← e₂, ← h]
    have e₃ := LinearMap.congr_fun (Units.inv_mul u₃) (B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y))
    rw [Module.End.mul_apply, Module.End.one_apply] at e₃
    exact e₃
  induction n using Int.induction_on generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinv, ih]

end GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem phiU_zpow_dmul : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht _ _ _ n x y
  exact units_zpow_bilin_comm (dmul P ρs ρt ρm χ hm ht) (phiU P ρs) (phiU P ρm) (phiU P ρt)
    (fun x y => phiD_dmul P ρs ρt ρm χ hm ht x y) n x y

end GlobalTheory.Pst.TwistLetters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecompositionStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sixth_decomposition : CentredStringDecomposition := by
  first | exact @GlobalTheory.StringDecomp.stringDecomp_holds | exact GlobalTheory.StringDecomp.stringDecomp_holds | (intros; apply GlobalTheory.StringDecomp.stringDecomp_holds <;> assumption)
end

