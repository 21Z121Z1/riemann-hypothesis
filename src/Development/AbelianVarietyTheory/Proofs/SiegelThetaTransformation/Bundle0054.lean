import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacter
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensLatMove

variable {D : D7}

def emb (D : D7) : AfE D →ₗ[D.host.F] AE D :=
  TensorProduct.map (GlobalTheory.AdelicLatMove.finIncl D) LinearMap.id

theorem emb_tmul (e : D.host.E) (α : Af D.host.F) :
    emb D (α ⊗ₜ[D.host.F] e) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (x : AF D.host.F) (e : D.host.E) :
    Formalism.L2.Theta.finPart D (x ⊗ₜ[D.host.F] e) = (sndA D.host.F x) ⊗ₜ[D.host.F] e := rfl

theorem emb_mul (a : AE D) (x : AfE D) : emb D (Formalism.L2.Theta.finPart D a * x) = a * emb D x := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
    | tmul α f =>
      rw [finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, emb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def outer (S T : HSp D) (v : Fin S.rank → AfE D) (u : Fin T.rank → AfE D) : WO S T :=
  Matrix.of fun a k => emb D (u a * v k)

def outerHom (S T : HSp D) : (Fin S.rank → AfE D) →+ (Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun u => outer S T v u) (fun u u' => by
      ext i j
      simp only [outer, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]))
    (fun v v' => AddMonoidHom.ext fun u => by
      ext i j
      simp only [outer, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Matrix.of_apply, Matrix.add_apply,
        Pi.add_apply, map_add, mul_add])

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    α * β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem intAf_one : (1 : Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem outer_pure (S T : HSp D) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (α β : Af D.host.F) :
    outer S T (fun i => α ⊗ₜ[D.host.F] s i) (fun i => β ⊗ₜ[D.host.F] t i) =
      Matrix.of fun a k => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (vecMulVec s t k a) := by
  ext a k
  simp only [outer, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, vecMulVec_apply, mul_comm (t a)]

theorem outer_mem (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank)
    (v : Fin S.rank → AfE D) (hv : v ∈ hatV Λ) (u : Fin T.rank → AfE D) (hu : u ∈ hatV L) :
    outer S T v u ∈ hatA S T (tens Λ L) := by
  change outerHom S T v u ∈ _
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hu using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, intAf_mul hβ hα, vecMulVec x y, AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩,
        outer_pure S T x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem hatA_le (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank) (K : AddSubgroup (WO S T))
    (hK : ∀ v ∈ hatV Λ, ∀ u ∈ hatV L, outer S T v u ∈ K) : hatA S T (tens Λ L) ≤ K := by
  rw [hatA, AddSubgroup.closure_le]
  rintro _ ⟨α, hα, y, hy, rfl⟩
  change _ ∈ K
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hy
    have e := outer_pure S T s t 1 α
    rw [mul_one] at e
    rw [← e]
    exact hK _ (AddSubgroup.subset_closure ⟨1, intAf_one, s, hs, rfl⟩) _
      (AddSubgroup.subset_closure ⟨α, hα, t, ht, rfl⟩)
  | zero =>
    convert zero_mem K using 1
    ext a k
    simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext a k
    simp [TensorProduct.tmul_add]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext a k
    simp [TensorProduct.tmul_neg]

theorem actO_outer (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (v : Fin S.rank → AfE D)
    (u : Fin T.rank → AfE D) :
    actO S T h g (outer S T v u) = outer S T (fmtC S h *ᵥ v) (fmt T g *ᵥ u) := by
  have key := GlobalTheory.AdelicLatMove.gram_mul_inv S h
  have h1 : S.gram.map (incA D) = 1 := by rw [hS, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.mul_one] at key
  ext i j
  simp only [actO, key, outer, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [← emb_mul, ← map_sum, mul_comm (emb D _)]
  congr 1
  simp only [fmt, fmtC, Formalism.L2.Theta.cM, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

def actHom (S T : HSp D) (h : GA D S) (g : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T h g) (fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul])

theorem mem_hatA_iff (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank)
    (L L' : Lt D.host.E T.rank) (h1 : IsMov (fmtC S h) Λ Λ') (h2 : IsMov (fmt T g) L L') (u : WO S T) :
    u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀ := by
  constructor
  · intro hu
    have := hatA_le S T Λ' L' ((hatA S T (tens Λ L)).map (actHom S T h g)) (fun v hv w hw => by
      obtain ⟨v₀, hv₀, rfl⟩ := (h1 v).1 hv
      obtain ⟨w₀, hw₀, rfl⟩ := (h2 w).1 hw
      exact ⟨_, outer_mem S T Λ L v₀ hv₀ w₀ hw₀, actO_outer S T hS h g v₀ w₀⟩) hu
    obtain ⟨u₀, hu₀, e⟩ := this
    exact ⟨u₀, hu₀, e.symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    refine hatA_le S T Λ L ((hatA S T (tens Λ' L')).comap (actHom S T h g)) (fun v hv w hw => ?_) hu
    change actO S T h g _ ∈ hatA S T (tens Λ' L')
    rw [actO_outer S T hS]
    exact outer_mem S T Λ' L' _ ((h1 _).2 ⟨v, hv, rfl⟩) _ ((h2 _).2 ⟨w, hw, rfl⟩)

theorem hatA_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  intro D S T C h g Λ Λ' L L' h1 h2
  have hΛ := mem_hatA_iff S T C.m.gS h g Λ Λ' L L' h1 h2
  refine ⟨hΛ, fun om hW f hth hlat => ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hW.om_heis h g _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e h⁻¹ g⁻¹ hh
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hW.om_heis h g _ f hth, hlat.2 e he u₀ hu₀ h0]

end GlobalTheory.TensLatMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedTensorLattice_strongApprox_open_compact : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank), (Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤) → (L.FG ∧ Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) → (∀ u, IsFinPt u → ∃ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, u - finW S T y ∈ hatA S T (tens Λ L)) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y ∈ hatA S T (tens Λ L) ↔ y ∈ tens Λ L) ∧ (∀ u ∈ hatA S T (tens Λ L), IsFinPt u ∧ ∀ N : ℕ, 0 < N → ∃ y ∈ tens Λ L, ∃ u' ∈ hatA S T (tens Λ L), u = finW S T y + N • u') ∧ (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens Λ L), N • u ∈ U) ∧ (∀ N : ℕ, 0 < N → IsOpen {w : WO S T | ∃ u ∈ hatA S T (tens Λ L), IsRealPt (w - N • u)}) ∧ IsCompact (hatA S T (tens Λ L) : Set (WO S T)) := by
  first | exact @GlobalTheory.Ker.HatLat.hatA_tens | exact GlobalTheory.Ker.HatLat.hatA_tens | (intros; apply GlobalTheory.Ker.HatLat.hatA_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacterStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eq_hermitian_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ : Lt E r, SelfD X L₁ → SelfD X L₂ → ∀ M : ℕ, 0 < M → ∀ v₁ v₂ : TF n g, IsVac X bas w (tens (stdL E n) L₁) v₁ → IsVac X bas w (tens (stdL E n) L₂) v₂ → ∃ (β : Matrix (Fin r) (Fin r) E) (t : ℂ), ccT β = β ∧ ∀ Λ ∈ Vset E n M, ∀ x, dbl X bas idx (unitv (projA X bas w (tens Λ L₁) v₁)) (unitv (projA X bas w (tens Λ L₂) v₂)) x = if x ∈ tens Λ (L₁ ⊔ L₂) then t * cexp (π * I * ((Algebra.trace ℚ E (x * β * ccT x).trace : ℚ) : ℂ)) else 0 := by
  first | exact @GlobalTheory.SW.dbl_vacuum | exact GlobalTheory.SW.dbl_vacuum | (intros; apply GlobalTheory.SW.dbl_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsM (D : D7) (T : Core D) (h : LawsM T) : GamAt T := by
  intro j hj σ hσ k γ hst hc
  obtain ⟨hgood, hA, -, -, -, -, hrest⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hrest j hj).2.1
  have hpins := h.pins
  unfold Formalism.L2.Pj.Par.Pins at hpins
  have hlev := hpins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at hlev
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hlev.1
  have h3 : 3 ≤ T.Q.l.M := by
    obtain ⟨p, hlt, hp⟩ := Nat.exists_infinite_primes (T.Q.l.M + 1)
    have h0 : T.Q.l.M.factorization p = 0 := Nat.factorization_eq_zero_of_lt (by omega)
    have := hgood p hp
    simpa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt, h0] using this
  have hU := (Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 (h.unf j hj σ hσ)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ :=
    GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ _ _ _ hU hA hr k γ hst hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hc' : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x =
        ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) • y := by
    rw [← hM]; exact hc
  have hu1 : u = 1 :=
    GlobalTheory.PrincCore.root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
      (h.muUnit j hj σ hσ) (D.host.g 0 * D.host.g 1) (hM ▸ h3) (h.levelK j hj σ hσ) k γ γ' hγ' hc' u n hn hu he
  have hγγ : γ' = γ := by
    ext a b
    have := congrFun (congrFun he a) b
    simpa [hu1] using this
  exact hγγ ▸ hγ'

theorem gamAt_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → GamAt T.toCore := by
  intro D T h
  exact gamAt_of_lawsM D T.toCore h.toLawsM

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D}

theorem EFR_conj (C : Ctx S T) (x y : RW T S) :
    EFR C.X (fun σ k a => conj (x (C.m.e.symm σ) a k) : WR C.X S.rank) (fun σ k a => conj (y (C.m.e.symm σ) a k)) =
      -omO S T x y := by
  simp only [EFR, hermC, omO, LinearMap.mk₂_apply, formAt]
  rw [← C.m.e.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.symm_apply_apply, C.m.e_emb, C.m.ka, C.m.gT, C.m.gS, inv_one,
    ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply, RCLike.conj_conj]
  have hx : (-(2 * D.host.xi0 / 2)) = -D.host.xi0 := by ring
  have hone : ∀ F : Fin S.rank → Fin S.rank → ℂ,
      ∑ a, ∑ b, tauE D τ ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) a b) * F a b = ∑ a, F a a := by
    intro F; simp [Matrix.one_apply]
  rw [hx]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hone, ← Complex.re_sum, ← Finset.mul_sum]
  have hc : conj (tauE D τ (-D.host.xi0)) *
      ∑ k, ∑ a, conj (x τ a k) * ∑ b, conj (tauE D τ (T.gram b a)) * y τ b k =
      conj (-(tauE D τ D.host.xi0 *
        ∑ k, ∑ b, conj (y τ b k) * ∑ a, tauE D τ (T.gram b a) * x τ a k)) := by
    simp only [map_neg, map_mul, map_sum, RCLike.conj_conj, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hc, Complex.conj_re, Complex.neg_re]
  ring

theorem pi_lineAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  obtain ⟨-, -, h⟩ := isLineAt_lineAt hθ τ z
  funext τ' i j
  have h1 := congrFun (congrFun (h 1 τ') i) j
  rw [Pi.single_apply]
  split_ifs at h1 ⊢ with hτ
  · rw [Complex.ofReal_one, one_smul] at h1
    exact h1
  · exact h1

theorem single_conj (C : Ctx S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) =
      fun σ k a => conj (piW C.θ T S (lineAt C.θ τ z 1) (C.m.e.symm σ) a k) := by
  rw [pi_lineAt C.inf]
  funext σ k a
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> simp

theorem dRho_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  intro D S T C f hf τ z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  have hθ := C.inf
  have hψ := C.std
  have hD' : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ),
      dRho (heisO C.ψ S T) C.θ τ z g =
        hD (iotaW σ T S) (piW C.θ T S) (omO S T) (piW C.θ T S (lineAt C.θ τ z 1)) g := by
    intro τ z g
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ z)]
  have hsm : ∀ g, C.IsTh g → Sm (iotaW σ T S) g := fun g hg => theta_sm hσ hg
  have hform : ∀ g, C.IsTh g → ∀ (u : RW T S) (w : WO S T),
      hD (iotaW σ T S) (piW C.θ T S) (omO S T) u g w =
        -(Real.pi * Complex.I) * (omO S T (piW C.θ T S w) u : ℝ) * g w +
          fderiv ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 u :=
    fun g hg u w => hD_eq_fderiv _ _ _ g (hsm g hg) u w
  have hdiff : ∀ g, C.IsTh g → ∀ w : WO S T,
      DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun g hg w => ((hsm g hg w).differentiable (by simp)) 0
  refine ⟨theta_dRho hθ hψ τ z hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0
    rw [map_zero, heisO_zero, ← dRho_eq_dLine] at h
    exact h
  · intro f' hf'
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f' hf', hform (f + f') (theta_add hf hf')]
    rw [show (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        (fun x => f (w + iotaW σ T S x)) + (fun x => f' (w + iotaW σ T S x)) from rfl,
      fderiv_add (hdiff f hf w) (hdiff f' hf' w)]
    simp only [Pi.add_apply, _root_.add_apply]
    ring
  · intro a
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform (a • f) (theta_smul a hf)]
    rw [show (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        (fun x => a * f (w + iotaW σ T S x)) from rfl, fderiv_const_mul (hdiff f hf w)]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
    ring
  · intro z'
    have hadd : piW C.θ T S (lineAt C.θ τ (z + z') 1) =
        piW C.θ T S (lineAt C.θ τ z 1) + piW C.θ T S (lineAt C.θ τ z' 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, e, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f hf, hform f hf, hadd, map_add,
      ContinuousLinearMap.map_add]
    push_cast
    ring
  · intro t
    have hs : piW C.θ T S (lineAt C.θ τ ((t : ℂ) • z) 1) = t • piW C.θ T S (lineAt C.θ τ z 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp [Complex.real_smul]
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform f hf, hs, map_smul, ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · intro u hu
    exact GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f
  · intro τ' z'
    have hskew : ∀ u v : RW T S, omO S T v u = -omO S T u v := by
      intro u v
      have h := omO_self hσ (u + v)
      simp only [map_add, LinearMap.add_apply, omO_self hσ, zero_add, add_zero] at h
      linarith
    simp only [hD']
    rw [heisenberg_derivative_commutator (WO S T) (RW T S) (iotaW σ T S) (piW C.θ T S) (omO S T)
      (hσ.pi_iota T S) (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) hskew f (hsm f hf),
      single_conj C τ z, single_conj C τ' z', EFR_conj]
    congr 1
    push_cast
    ring

end GlobalTheory.Ker.HeisDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabOpen

noncomputable def stab {D : D7} (V : HSp D) (L : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) :
    Subgroup (GA D V) where
  carrier := {h | ∀ y, y ∈ L ↔ (finHom V h).1.mulVec y ∈ L}
  one_mem' := fun y => by rw [map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    rw [ha ((finHom V a⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

theorem isOpen_stab_latHat : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  intro D V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have e : Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) =
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    rfl
  rw [e]
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp 1 one_pos
  have hc := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [map_one, Units.val_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, map_one, Units.val_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds (stab V (GlobalTheory.AdLat.hat D.host.F
    (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))) (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end GlobalTheory.StabOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_group_structure : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ e : {ga : GL (Fin T.rank) D.host.E // IsUn C.X ga} ≃ GQ T, ∀ ga, IsRatOf T ga.1 (e ga).1) ∧ (∀ (γ γ' : GA D T) ga ga', IsRatOf T ga γ → IsRatOf T ga' γ' → IsRatOf T (ga * ga') (γ * γ') ∧ IsRatOf T ga⁻¹ γ⁻¹ ∧ γ ∈ GQ T ∧ IsUn C.X ga ∧ (γ = γ' ↔ ga = ga')) ∧ (∃ e : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ GQ S, ∀ h, cM (mt S (e h).1) = h.1.map (incA D)) ∧ ∀ V : HSp D, Countable (GQ V) ∧ (∀ g g' : GA D V, mt V (g * g') = mt V g * mt V g' ∧ fmt V (g * g') = fmt V g * fmt V g' ∧ fmtC V (g * g') = fmtC V g * fmtC V g' ∧ (mt V g = mt V g' → g = g')) ∧ (∀ g : GA D V, ∃ a ∈ GinfC V, ∃ f ∈ GfC V, g = a * f) ∧ (∀ a ∈ GinfC V, fmt V a = 1 ∧ fmtC V a = 1 ∧ ∀ f ∈ GfC V, a * f = f * a) ∧ ∀ (I : Ideal (𝓞 D.host.F)), I ≠ ⊥ → ∀ f ∈ GfC V, ∃ f₁ ∈ GfC V, ∃ f₂ ∈ GfC V, f = f₁ * f₂ ∧ f₁ * f₂ = f₂ * f₁ ∧ TrivAt V I f₁ ∧ TrivOff V I f₂ := by
  first | exact @GlobalTheory.Ker.Grp.rational_points_and_parts | exact GlobalTheory.Ker.Grp.rational_points_and_parts | (intros; apply GlobalTheory.Ker.Grp.rational_points_and_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_fundamentalDomain_innerProduct_basic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f, C.IsTh f → (∃ b : ℝ, ∀ w, ‖f w‖ ≤ b) ∧ (ipO μ 𝓕 f f = 0 → f = 0) ∧ ipO μ 𝓕 f f = nrm2 μ 𝓕 f ∧ ∀ f', C.IsTh f' → IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ ∧ ipO μ 𝓕 f' f = conj (ipO μ 𝓕 f f') ∧ (∀ a : ℂ, ipO μ 𝓕 (a • f) f' = a * ipO μ 𝓕 f f') ∧ (∀ f'', C.IsTh f'' → ipO μ 𝓕 (f + f') f'' = ipO μ 𝓕 f f'' + ipO μ 𝓕 f' f'') ∧ (∀ w, ipO μ 𝓕 (C.rho w f) (C.rho w f') = ipO μ 𝓕 f f') ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ p, ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f' := by
  first | exact @GlobalTheory.Ker.ScalarProduct.ip_basic | exact GlobalTheory.Ker.ScalarProduct.ip_basic | (intros; apply GlobalTheory.Ker.ScalarProduct.ip_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliserStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  first | exact @GlobalTheory.Dict.mult_eq_one_on_stab | exact GlobalTheory.Dict.mult_eq_one_on_stab | (intros; apply GlobalTheory.Dict.mult_eq_one_on_stab <;> assumption)
end

