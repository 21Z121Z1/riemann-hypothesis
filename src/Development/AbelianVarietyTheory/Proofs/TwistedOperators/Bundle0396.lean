import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TensIrr

theorem eq_smul_of_ann {V : Type} [AddCommGroup V] [Module ℂ V] (SV : Set (Module.End ℂ V))
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤)
    (v₀ w : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ a ∈ Algebra.adjoin ℂ SV, a v₀ = 0 → a w = 0) : ∃ c : ℂ, w = c • v₀ := by
  let A := Algebra.adjoin ℂ SV
  let ev : V → (A →ₗ[ℂ] V) := fun y =>
    { toFun := fun a => (a : Module.End ℂ V) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y := fun _ _ => rfl
  have hsurj : Function.Surjective (ev v₀) := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact ⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0
    · exfalso; apply hv₀
      have h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀) := LinearMap.mem_range_self _ _
      rw [h0, Submodule.mem_bot] at h1
      simpa [hev] using h1
    · exact h0
  have hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w) := fun a ha => by
    rw [LinearMap.mem_ker, hev] at ha ⊢
    exact h a a.2 ha
  let φ : Module.End ℂ V := ((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp
    (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap
  have hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w := by
    intro a
    have h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hev v₀, h2, Submodule.liftQ_apply, hev]
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank
    (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by
      ext y
      obtain ⟨a, rfl⟩ := hsurj y
      have h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w :=
        hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩
      simp only [Module.End.mul_apply, hev] at h1 ⊢
      rw [h1, hφ a])
  refine ⟨c, ?_⟩
  have h3 := hφ 1
  simp only [OneMemClass.coe_one, Module.End.one_apply] at h3
  rw [← h3, hc]
  simp

theorem rTensor_mem_adjoin {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (SV : Set (Module.End ℂ V)) (N : Submodule ℂ (V ⊗[ℂ] U))
    (hN : ∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hN a ha
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
    simpa using N.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem tensor_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x₁, hx₁N, hx₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ U
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n := ⟨_, x₁, hx₁N, hx₁, rfl⟩
  obtain ⟨x, hxN, hx0, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0 := by
    intro y hy hlt
    by_contra hy0
    exact Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩
  obtain ⟨j₀, hj₀⟩ : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (LinearEquiv.map_ne_zero_iff e).mpr hx0
  set v₀ := e x j₀ with hv₀def
  have hv₀ : v₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have hA := rTensor_mem_adjoin SV N hNV
  have hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀ := by
    intro j
    refine eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)
    have hy := hmin _ (hA a ha x hxN) (by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j₀, hj₀, ?_⟩
        rw [Finsupp.mem_support_iff, not_not, he]
        exact hav
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [he, h0, map_zero])
    have h5 := he a x j
    rw [hy, map_zero, Finsupp.zero_apply] at h5
    exact h5.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv₀
  let u : U := b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))
  have hxu : x = v₀ ⊗ₜ u := by
    apply e.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    obtain ⟨c, hc⟩ := hcol j
    rw [hc, map_smul, hℓ, smul_eq_mul, mul_one]
  have hu : u ≠ 0 := by
    intro hu0
    apply hx0
    rw [hxu, hu0, TensorProduct.tmul_zero]
  have hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤ := by
    rcases hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by
      simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
      have h6 := hNV a ha _ hv
      rwa [LinearMap.rTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
        rw [← hxu]; exact hxN
      rw [h0, Submodule.mem_bot] at h7
      exact hv₀ h7
    · exact h0
  have hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤ := by
    intro v
    rcases hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by
      simp only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢
      have h6 := hNU c hc _ hy
      rwa [LinearMap.lTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v) := by
        have h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by rw [hP]; trivial
        simpa using h8
      rw [h0, Submodule.mem_bot] at h7
      exact hu h7
    · exact h0
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m) := by rw [hQ m]; trivial
  simpa using h9

end GlobalTheory.TensIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.ModGrowth

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation in

def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) (u : UB J) :
    GA D V :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.cA D) u.1, by
    have hu : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u)ᵀ * incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D) = incM J := u.2
    have hJ : incM J = -incM V.gram := by
      subst h; ext i j; simp [incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hu
    show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D))ᵀ *
      incM V.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D) = incM V.gram
    have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u :=
      Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
    rw [e]; exact hu⟩

theorem conjInv_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram)
    (g : GA D V) : conjInv V h (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h g) = g :=
  Subtype.ext (Units.ext (Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _))

theorem conjU_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram)
    (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h (conjInv V h u) = u :=
  Subtype.ext (Units.ext (Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _))

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) :
    Continuous (conjInv V h) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

def conjHomeo (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) :
    GA D V ≃ₜ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h
  invFun := conjInv V h
  left_inv := conjInv_conjU V h
  right_inv := conjU_conjInv V h
  continuous_toFun := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V (-1) h
  continuous_invFun := continuous_conjInv V h

theorem measurableEmbedding_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : J = (-1 : D.host.E) • V.gram) : MeasurableEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h) := by
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  exact (conjHomeo V h).measurableEmbedding

end GlobalTheory.ModGrowth

namespace GlobalTheory.ModGrowth

variable {D : D7}

theorem ht_kapX_le (θ : InfFam D) (hθ : IsInfFam θ) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) :
    ∃ C : NNReal, ∀ h : GA D X, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (kapX X e hJ h) ≤ C * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h := by
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.infiniteHeight_transposeGramUnitary_le D θ hθ X e hJ
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.finprod_finiteHeight_transposeGramUnitary_le D X e hJ
  refine ⟨C₁ * C₂, fun h => ?_⟩
  show (∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1)) *
      ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
    C₁ * C₂ * ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h) * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h)
  calc _ ≤ (C₁ * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h) * (C₂ * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h) :=
        mul_le_mul' (h₁ h) (h₂ h)
    _ = _ := by ring

end GlobalTheory.ModGrowth

namespace GlobalTheory.ModGrowth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem modInt_of_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → IsHaarFD W₁ ν₁ 𝓕₁ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Φ₀ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Γ.M'.Conv om' Φ₀D →
    (∃ (C : ℝ) (k : ℕ), ∀ g h, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₀D g h‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht h : ℝ) ^ k) →
    ModInt θ ωB ν₁ 𝓕₁ Φ₀ := by
  intro D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hH _ Φ₀ Φ₀D hD hC hB
  obtain ⟨C, k, hCk⟩ := hB
  obtain ⟨C', hC'⟩ := ht_kapX_le θ hθ X e hO.JX
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hvol : ν₁ 𝓕₁ < ⊤ :=
    GlobalTheory.Mem.VolFin.finVol _ _ D.sp.cm.sig hcm.1 W₁.rank W₁.gram (hcm.2 W₁) ν₁ hH.1 𝓕₁ hH.2
  have hemb := measurableEmbedding_conjU W₁ hO.JW₁
  have key : ∀ g h, thetaKO ωB g h Φ₀ =
      theta om' Φ₀D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ g) (kapX X e hO.JX h) := fun g h =>
    (hO.theta_eq_B hD g h).symm
  refine ⟨k, max C 0 * (C' : ℝ) ^ k * ν₁.real 𝓕₁, fun h => ⟨?_, ?_⟩⟩
  · have hi := hC (kapX X e hO.JX h)
    rw [hO.measW₁, hO.domW₁, hemb.integrableOn_map_iff, Set.preimage_image_eq _ hemb.injective] at hi
    have hf : (fun g => thetaKO ωB g h Φ₀) =
        (fun u => theta om' Φ₀D u (kapX X e hO.JX h)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ :=
      funext fun g => key g h
    rw [hf]; exact hi
  · have hht : (ht (kapX X e hO.JX h) : ℝ) ≤ (C' : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by
      exact_mod_cast hC' h
    have hb : ∀ g ∈ 𝓕₁, ‖‖thetaKO ωB g h Φ₀‖‖ ≤
        max C 0 * ((C' : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ)) ^ k := by
      intro g _
      rw [norm_norm, key]
      calc _ ≤ C * (ht (kapX X e hO.JX h) : ℝ) ^ k := hCk _ _
        _ ≤ max C 0 * (ht (kapX X e hO.JX h) : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hht k) (le_max_right _ _)
    have hI := norm_setIntegral_le_of_norm_le_const hvol hb
    calc _ ≤ ‖∫ g in 𝓕₁, ‖thetaKO ωB g h Φ₀‖ ∂ν₁‖ := Real.le_norm_self _
      _ ≤ _ := hI
      _ = _ := by rw [mul_pow]; ring

end GlobalTheory.ModGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtOrth

theorem of_sizes (lemM1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C)
  (lemM2 : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N)
  (lemM3 : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ, ∀ (h : GA D A) (η : Fin A.rank → D.host.E), GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η))
  (lemH : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a) :
    ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  intro D S A B o
  obtain ⟨C1, b, hM1⟩ := lemM1 D A
  obtain ⟨c, N, hc, hM2⟩ := lemM2 D S
  obtain ⟨C3, hM3⟩ := lemM3 D S A B o
  obtain ⟨C2, a2, hH⟩ := lemH D S A B o
  set K : ℝ := max (max C3 c) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hC3K : C3 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hcK : c ≤ K := (le_max_right _ _).trans (le_max_left _ _)

  have first : ∀ h, quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := by
    intro h
    set H := quotHeight S (o.emb (h, 1))
    have hH1 : 1 ≤ H := one_le_quotHeight S _
    have hHN : 1 ≤ H ^ N := one_le_pow₀ hH1
    have hKH : 0 < K * H ^ N := mul_pos hK0 (zero_lt_one.trans_le hHN)
    set t := c / (K * H ^ N)
    have ht0 : 0 < t := div_pos hc hKH
    have ht1 : t ≤ 1 := (div_le_one hKH).2 (hcK.trans (le_mul_of_one_le_right hK0.le hHN))
    have hshort : ∀ η : Fin A.rank → D.host.E, η ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
      intro η hη
      have hne : o.iA *ᵥ η ≠ 0 := by
        intro h0
        apply hη
        have := congrArg (fun x => o.qA *ᵥ x) h0
        simpa [Matrix.mulVec_mulVec, o.qA_iA] using this
      have h2 := hM2 (o.emb (h, 1)) _ hne
      have h3 := hM3 h η
      have hv := GlobalTheory.HtOrth.vsize_nonneg (GlobalTheory.HtOrth.seen A h η)
      rw [div_le_iff₀ hKH]
      calc c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) * H ^ N := h2
        _ ≤ C3 * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right h3 (zero_le_one.trans hHN)
        _ ≤ K * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3K hv) (zero_le_one.trans hHN)
        _ = _ := by ring
    have h1 := hM1 h t ht0 ht1 hshort
    have htb : 0 < t ^ b := pow_pos ht0 b
    have e : t ^ b * ((K / c) ^ b * H ^ (N * b)) = 1 := by
      rw [← mul_assoc, ← mul_pow, pow_mul]
      have : t * (K / c) = (H ^ N)⁻¹ := by
        simp only [t]; field_simp
      rw [this, ← mul_pow, inv_mul_cancel₀ (zero_lt_one.trans_le hHN).ne', one_pow]
    calc quotHeight A h = quotHeight A h * t ^ b * ((K / c) ^ b * H ^ (N * b)) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ C1 * ((K / c) ^ b * H ^ (N * b)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring

  have second : ∀ h, quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := by
    intro h
    have hC2 : 0 ≤ C2 := by
      have := hH 1
      rw [show ((1 : GA D A), (1 : GA D B)) = 1 from rfl, map_one, height_one, height_one, one_pow, mul_one] at this
      linarith
    obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight A h
    have hγS : o.emb (γ, 1) ∈ GQ S := by
      rw [mem_GQ_iff] at hγ ⊢
      rw [o.mt_emb, mt_one, Matrix.mul_one]
      exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) hγ) (rat_mem _)) (ratMx_mul (rat_mem _) (rat_mem _))
    have e : o.emb (γ * h, 1) = o.emb (γ, 1) * o.emb (h, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    calc quotHeight S (o.emb (h, 1)) ≤ height S (o.emb (γ, 1) * o.emb (h, 1)) := quotHeight_le S _ hγS
      _ = height S (o.emb (γ * h, 1)) := by rw [e]
      _ ≤ C2 * height A (γ * h) ^ a2 := hH _
      _ ≤ C2 * (2 * quotHeight A h) ^ a2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos A _).le h2 _) hC2
      _ = _ := by ring

  refine ⟨max (C1 * (K / c) ^ b) (C2 * 2 ^ a2), max (N * b) a2, fun h => ⟨?_, ?_⟩⟩
  · have hx : 1 ≤ quotHeight S (o.emb (h, 1)) := one_le_quotHeight S _
    have hq := first h
    have hpos : 0 ≤ C1 * (K / c) ^ b := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) (N * b))
      linarith [quotHeight_pos A h]
    calc quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight S (o.emb (h, 1)) ^ (max (N * b) a2) :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hx (le_max_left _ _)) (by positivity)
            (hpos.trans (le_max_left _ _))
  · have hx : 1 ≤ quotHeight A h := one_le_quotHeight A h
    have hq := second h
    have hpos : 0 ≤ C2 * 2 ^ a2 := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) a2)
      linarith [quotHeight_pos S (o.emb (h, 1))]
    calc quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight A h ^ (max (N * b) a2) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hx (le_max_right _ _)) (by positivity)
            (hpos.trans (le_max_right _ _))

theorem quotHeight_orthDec_cmp : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h,
    quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a :=
  of_sizes GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow GlobalTheory.T.adelicVectorSize_seen_orthogonalSummand_le GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow

end GlobalTheory.HtOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationsForTripleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representations_for_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA ∧ IsWeil ψ false W₁ X α (α / β) ωB := by
  first | exact @GlobalTheory.SquareComm.WeilOfTriple.exists_weil_pair | exact GlobalTheory.SquareComm.WeilOfTriple.exists_weil_pair | (intros; apply GlobalTheory.SquareComm.WeilOfTriple.exists_weil_pair <;> assumption)
end

