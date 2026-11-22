import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedCoord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def coord (S T : HSp D) : WO S T ≃+ WA S T where
  toFun := toTWsmall S T
  invFun y := HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D))
  left_inv x := by
    simp only [toTWsmall, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv y := by
    simp only [toTWsmall]
    rw [Matrix.mul_assoc, mul_gramInv, Matrix.mul_one, Matrix.transpose_transpose]
  map_add' x y := by
    simp only [toTWsmall]
    rw [Matrix.add_mul, Matrix.transpose_add]

theorem coord_apply (S T : HSp D) (x : WO S T) :
    coord S T x = (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D)))ᵀ := rfl

theorem coord_symm_apply (S T : HSp D) (y : WA S T) :
    (coord S T).symm y = HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D)) := rfl

theorem continuous_coord (S T : HSp D) : Continuous (coord S T) :=
  (continuous_id.matrix_mul continuous_const).matrix_transpose

theorem continuous_coord_symm (S T : HSp D) : Continuous (coord S T).symm :=
  continuous_id.matrix_transpose.matrix_mul continuous_const

theorem coord_ratW (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    coord S T (ratW T S γ) = ratW S T (γ * S.gram⁻¹)ᵀ := by
  rw [coord_apply]
  unfold ratW
  rw [← Matrix.map_mul, Matrix.transpose_map]

theorem coord_symm_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    (coord S T).symm (ratW S T γ) = ratW T S (γᵀ * S.gram) := by
  rw [coord_symm_apply]
  unfold ratW
  rw [Matrix.map_mul, Matrix.transpose_map]

theorem coord_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (x : WO S T) (h : x.map φ = 0) :
    (coord S T x).map φ = 0 := by
  rw [coord_apply, Matrix.transpose_map, Matrix.map_mul, h, Matrix.zero_mul, Matrix.transpose_zero]

theorem coord_symm_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (y : WA S T) (h : y.map φ = 0) :
    ((coord S T).symm y).map φ = 0 := by
  rw [coord_symm_apply, Matrix.map_mul, Matrix.transpose_map, h, Matrix.transpose_zero, Matrix.zero_mul]

theorem symplOH_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    symplOH S T x y = symplH S T (coord S T x) (coord S T y) := by
  unfold symplOH symplH
  rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1 x y]
  rfl

theorem heisO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ) :
    heisO ψ S T w (fun x => f (coord S T x)) = fun x => Heisenberg₂ ψ S T (coord S T w) f (coord S T x) := by
  funext x
  simp only [heisO, Formalism.L2.Theta.Heisenberg₂, map_add, symplOH_eq S T hr]

theorem isThetaFunO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ) :
    IsThetaFunO ψ S T (fun x => f (coord S T x)) ↔ IsThetaFun ψ S T f := by
  have c1 := continuous_coord S T
  have c2 := continuous_coord_symm S T
  refine ⟨fun hf => ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩,
    fun hf => ⟨fun γ w => ?_, ?_, hf.cont.comp c1, fun k L hL h0 w => ?_⟩⟩
  · have := hf.quasi (γᵀ * S.gram) ((coord S T).symm w)
    rw [← coord_symm_ratW, symplOH_eq S T hr] at this
    simpa only [map_add, AddEquiv.apply_symm_apply] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).symm.toAddMonoidHom, hU.preimage c2, fun u hu h0 => ?_⟩
    have := hfix ((coord S T).symm u) hu (coord_symm_map_zero S T _ u h0)
    rw [heisO_coord S T hr] at this
    funext y
    simpa only [AddEquiv.apply_symm_apply] using congrFun this ((coord S T).symm y)
  · simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using hf.cont.comp c2
  · have := hf.smooth k ((coord S T).symm.toAddMonoidHom.comp L) (c2.comp hL)
      (fun t => coord_symm_map_zero S T _ _ (h0 t)) ((coord S T).symm w)
    simpa only [map_add, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] using this
  · have := hf.quasi (γ * S.gram⁻¹)ᵀ (coord S T w)
    rw [← coord_ratW, ← symplOH_eq S T hr] at this
    simpa only [map_add] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).toAddMonoidHom, hU.preimage c1, fun u hu h0 => ?_⟩
    rw [heisO_coord S T hr, hfix (coord S T u) hu (coord_map_zero S T _ u h0)]
  · have := hf.smooth k ((coord S T).toAddMonoidHom.comp L) (c1.comp hL)
      (fun t => coord_map_zero S T _ _ (h0 t)) (coord S T w)
    simpa only [map_add, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe] using this

theorem coord_gen (S T : HSp D) (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    coord S T (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * star (s i) * t j) := by
  rw [← AddEquiv.eq_symm_apply, coord_symm_apply]
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : incA D (S.gram k j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j := rfl
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem coord_mem_latVWS (S T : HSp D) (hr : S.rank ≤ T.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z)) : coord S T u ∈ latVWS S T Z := by
  have : latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) ≤ (latVWS S T Z).comap (coord S T).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, fun v hv => h0 v (not_not.2 hv), a, ha, s, hs, t, ht, ?_⟩
    simp only [if_pos hr]
    exact coord_gen S T _ a s t
  exact this hu

theorem exists_coord : ∀ (D : D7) (S T : HSp D), S.rank ≤ T.rank → ∃ e : WO S T ≃+ WA S T, Continuous e ∧ Continuous e.symm ∧ (∀ x, e x = toTWsmall S T x) ∧ (∀ x, e x ∈ ratL S T ↔ x ∈ ratL T S) ∧ (∀ (a : AE D) (x : WO S T), e (a • x) = a • e x) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ), heisO ψ S T w (fun x => f (e x)) = fun x => Heisenberg₂ ψ S T (e w) f (e x)) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ), IsThetaFunO ψ S T (fun x => f (e x)) ↔ IsThetaFun ψ S T f) ∧ ∀ (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T), u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) → e u ∈ latVWS S T Z := by
  intro D S T hr
  refine ⟨coord S T, continuous_coord S T, continuous_coord_symm S T, fun _ => rfl, fun x => ⟨?_, ?_⟩, fun a x => ?_,
    heisO_coord S T hr, isThetaFunO_coord S T hr, coord_mem_latVWS S T hr⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ratW S T γ = coord S T x := hγ
    refine ⟨γᵀ * S.gram, ?_⟩
    change ratW T S _ = x
    rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
  · rw [coord_apply, coord_apply, Matrix.smul_mul, Matrix.transpose_smul]

end GlobalTheory.OrientedCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceHom

open GlobalTheory.PointAtPlace

variable {D : D7} {θ : InfF D}

theorem infMat_mul (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    infMat D.sp.cm.sig V.gram φ (a * b) = infMat D.sp.cm.sig V.gram φ a * infMat D.sp.cm.sig V.gram φ b :=
  archM_mul V φ a b

theorem infMat_one (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    infMat D.sp.cm.sig V.gram φ 1 = 1 := archM_one V φ

theorem atTau_spec (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau θ V τ g (atTau θ V τ g) := by
  have hu := existsUnique_isAtTau V τ θ hθ g hg
  unfold atTau
  rw [dif_pos hu.exists]
  exact hu.exists.choose_spec

theorem atTau_mem (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem one_mem_UH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem mul_mem_UH {n : ℕ} {H g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH H) : g * g' ∈ Formalism.QuantumDeterminants.UH H := by
  have h1 : gᴴ * H * g = H := hg
  have h2 : g'ᴴ * H * g' = H := hg'
  show (g * g')ᴴ * H * (g * g') = H
  calc (g * g')ᴴ * H * (g * g') = g'ᴴ * (gᴴ * H * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1, h2]

theorem atTau_one (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : atTau θ V τ 1 = 1 :=
  (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique (atTau_spec hθ V τ (one_mem_UH _))
    ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩

theorem atTau_mul (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g' := by
  have a := atTau_spec hθ V τ hg
  have b := atTau_spec hθ V τ hg'
  refine (existsUnique_isAtTau V τ θ hθ _ (mul_mem_UH hg hg')).unique (atTau_spec hθ V τ (mul_mem_UH hg hg'))
    ⟨mul_mem a.1 b.1, ?_, fun τ' h => ?_⟩
  · rw [infMat_mul, a.2.1, b.2.1]
  · rw [infMat_mul, a.2.2 τ' h, b.2.2 τ' h, Matrix.one_mul]

theorem comm_of_mem (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  have a2 : finHom V a = 1 := ha
  have k1 : infHom V k = 1 := hk
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ ?_ ?_)
  · show infHom V _ = 1
    simp only [map_mul, map_inv, k1, mul_one, one_mul, mul_inv_cancel]
  · show finHom V _ = 1
    simp only [map_mul, map_inv, a2, mul_one, one_mul, mul_inv_cancel]

open Classical in

theorem entry_eq {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V} (hh : IsAtTau θ V τ g h) (i j : Fin V.rank) :
    (matHom V h).1 i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have a2 : (finHom V h).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hh.1
    have e : finPart D ((matHom V h).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [RingHom.map_sub, RingHom.map_add, hσ.fin, e, add_zero, sub_self]
  · have e1 : θ τ' (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (infMat_one V (θ τ')) i) j
    have e2 : θ τ' (infPart D ((matHom V h).1 i j)) = infMat D.sp.cm.sig V.gram (θ τ') h i j := rfl
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_sub, RingHom.map_add, hσ.comp, e1, e2]
    by_cases c : τ' = τ
    · subst c
      rw [hh.2.1, Pi.single_eq_same]; ring
    · rw [hh.2.2 τ' c, Pi.single_eq_of_ne c]; ring

theorem isAtTau_inv (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau θ V τ g h) :
    IsAtTau θ V τ ((gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ) h⁻¹ := by
  have hu : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
    rw [this]
    exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
  have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h2 : (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
  have k : ∀ φ, infMat D.sp.cm.sig V.gram φ h * infMat D.sp.cm.sig V.gram φ h⁻¹ = 1 := fun φ => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  refine ⟨inv_mem hh.1, ?_, fun τ' c => ?_⟩
  · have := k (θ τ)
    rw [hh.2.1] at this
    rw [← Matrix.one_mul (infMat _ _ _ h⁻¹), ← h2, Matrix.mul_assoc _ g, this, Matrix.mul_one]
  · have := k (θ τ')
    rwa [hh.2.2 τ' c, Matrix.one_mul] at this

theorem continuousOn_atTau (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have key : ∀ (i j : Fin V.rank), Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
        σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := fun i j =>
    continuous_const.add (hσ.cont.comp ((continuous_single (A := fun _ : D.what₂.Tau => ℂ) τ).comp
      ((continuous_id.matrix_elem i j).sub continuous_const)))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((key i j).comp continuous_subtype_val).congr fun g => ?_
    exact (entry_eq hσ V τ (atTau_spec hθ V τ g.2) i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have c : Continuous fun g : Formalism.QuantumDeterminants.UH (gramAt D V τ) => (gramAt D V τ)⁻¹ * g.1ᴴ * gramAt D V τ :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const
    refine ((key i j).comp c).congr fun g => ?_
    exact (entry_eq hσ V τ (isAtTau_inv V τ g.2 (atTau_spec hθ V τ g.2)) i j).symm

theorem atTau_laws : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau), (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau θ V τ g h) ∧ atTau θ V τ 1 = 1 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧ (∀ g, ∀ k ∈ GfC V, atTau θ V τ g * k = k * atTau θ V τ g) ∧ ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  fun _ θ hθ V τ => ⟨fun g hg => existsUnique_isAtTau V τ θ hθ g hg, atTau_one hθ V τ,
    fun _ hg _ hg' => atTau_mul hθ V τ hg hg', fun g _ hk => comm_of_mem V (atTau_mem V τ g) hk,
    continuousOn_atTau hθ V τ⟩

end GlobalTheory.PointAtPlaceHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitary
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open Formalism.UG (cT cT_mul cT_one bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeRef

section Cong

variable {A : Type} [CommRing A] {M : ℕ} (s : A →+* A)

def act (J : Matrix (Fin M) (Fin M) A) (P : GL (Fin M) A) : Matrix (Fin M) (Fin M) A :=
  cT s (P : Matrix (Fin M) (Fin M) A) * J * (P : Matrix (Fin M) (Fin M) A)

theorem act_one (J : Matrix (Fin M) (Fin M) A) : act s J 1 = J := by
  simp [act, cT_one]

theorem act_mul (J : Matrix (Fin M) (Fin M) A) (P Q : GL (Fin M) A) :
    act s J (P * Q) = act s (act s J P) Q := by
  simp only [act, Units.val_mul, cT_mul, Matrix.mul_assoc]

def cong (M : ℕ) : Setoid (Matrix (Fin M) (Fin M) A) where
  r J J' := ∃ P : GL (Fin M) A, J' = act s J P
  iseqv := ⟨fun J => ⟨1, (act_one s J).symm⟩,
    fun ⟨P, h⟩ => ⟨P⁻¹, by rw [h, ← act_mul, mul_inv_cancel, act_one]⟩,
    fun ⟨P, h⟩ ⟨Q, h'⟩ => ⟨P * Q, by rw [h', h, act_mul]⟩⟩

end Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}

omit [NumberField E] in
theorem frameRel_iff (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (g : HA (AF F) σ J)
    (g' : HA (AF F) σ J') : FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g g' ↔
      HA.mat (AF F) σ J' g' = (bc (inclR (AF F)) P)⁻¹ * HA.mat (AF F) σ J g * bc (inclR (AF F)) P := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm, ← Units.val_inj]
  rfl

omit [NumberField E] in
theorem bc_mem {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : act (σ : E →+* E) J u = J) :
    bc (inclR (AF F)) u ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (u : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  have h : cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR, inclR]
  rw [h, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun X : Matrix (Fin M) (Fin M) E => X.map (inclR (F := F) (AF F))) hu

def IsTransport (σ : E →ₐ[F] E) (J₀ J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) : Prop :=
  ∃ (P : GL (Fin M) E) (e : HA (AF F) σ J₀ ≃* HA (AF F) σ J), J = act (σ : E →+* E) J₀ P ∧
    (∀ g, FrameRel J₀ J (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ μ = Measure.haar.map e

theorem frame (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (h : J' = act (σ : E →+* E) J P) :
    (∃ e : HA (AF F) σ J ≃* HA (AF F) σ J', ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧
    ∀ e : HA (AF F) σ J ≃* HA (AF F) σ J', (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) →
      Continuous e ∧ Continuous e.symm :=
  ⟨(GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).1.exists, (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).2⟩

theorem IsTransport.isHaar {J₀ J : Matrix (Fin M) (Fin M) E} {μ : Measure (HA (AF F) σ J)}
    (h : IsTransport σ J₀ J μ) : μ.IsHaarMeasure := by
  obtain ⟨P, e, hJ, he, rfl⟩ := h
  obtain ⟨h1, h2⟩ := (frame J₀ J P hJ).2 e he
  exact e.isHaarMeasure_map _ h1 h2

theorem IsTransport.map_eq (hσ : IsCMExt F E σ) {J₀ J J' : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : IsTransport σ J₀ J μ) (h' : IsTransport σ J₀ J' μ') {P : GL (Fin M) E} (hP : J' = act (σ : E →+* E) J P)
    (e : HA (AF F) σ J ≃* HA (AF F) σ J') (he : ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) :
    μ.map e = μ' := by
  haveI := h.isHaar
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.HermLineZeros.conj_invol hσ) (δ := σ d - d)
      (sub_ne_zero.2 hd) (by rw [map_sub, GlobalTheory.HermLineZeros.conj_invol hσ, neg_sub]) hJ μ
  obtain ⟨P₁, e₁, hJ₁, he₁, hμ⟩ := h
  obtain ⟨P₂, e₂, hJ₂, he₂, rfl⟩ := h'
  have hu : act (σ : E →+* E) J (P₁⁻¹ * P₂ * P⁻¹) = J := by
    conv_lhs => rw [hJ₁, ← act_mul, ← mul_assoc, mul_inv_cancel_left, act_mul, ← hJ₂, hP, ← act_mul,
      mul_inv_cancel, act_one]
  let u : HA (AF F) σ J := (⟨_, bc_mem hu⟩ : HR (AF F) σ J)
  have hc := ((frame J J' P hP).2 e he).1.measurable
  have hc₁ := ((frame J₀ J P₁ hJ₁).2 e₁ he₁).1.measurable
  have key : (e₂ : _ → _) = e ∘ ((fun x => x * u) ∘ (fun x => u⁻¹ * x)) ∘ e₁ := by
    funext g
    apply Subtype.ext
    have a := (frameRel_iff _ _ _ _ _).1 (he₂ g)
    have b := (frameRel_iff _ _ _ _ _).1 (he (u⁻¹ * e₁ g * u))
    have c := (frameRel_iff _ _ _ _ _).1 (he₁ g)
    refine a.trans (Eq.trans ?_ b.symm)
    show _ = _ * ((bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹))⁻¹ * HA.mat (AF F) σ J (e₁ g) *
      bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹)) * _
    rw [c]
    simp only [map_mul, map_inv]
    group
  have hl := measurable_const_mul u⁻¹
  have hr := measurable_mul_const u
  rw [key, ← Measure.map_map hc ((hr.comp hl).comp hc₁), ← Measure.map_map (hr.comp hl) hc₁, ← hμ,
    ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem exists_isTransport (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    ∃ μ, IsTransport σ (Quotient.mk (cong (σ : E →+* E) M) J).out J μ := by
  obtain ⟨P, hP⟩ := Quotient.mk_out (s := cong (σ : E →+* E) M) J
  obtain ⟨e, he⟩ := (frame (σ := σ) _ J P hP).1
  exact ⟨_, P, e, hP, he, rfl⟩

theorem exists_isHaar_basisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  intro F E _ _ _ _ _ σ hσ
  choose μ hμ using fun (M : ℕ) (J : Matrix (Fin M) (Fin M) E) => exists_isTransport σ J
  refine ⟨⟨μ⟩, fun M J _ => (hμ M J).isHaar, fun M J J' P hJ hP => ⟨(frame J J' P hP).1, fun e he => ?_⟩⟩
  have h' := hμ M J'
  rw [← Quotient.sound (s := cong (σ : E →+* E) M) (a := J) (b := J') ⟨P, hP⟩] at h'
  exact (hμ M J).map_eq hσ hJ h' hP e he

end GlobalTheory.GaugeRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
section
noncomputable section

namespace GlobalTheory.Mem.UnitaryEmb

open scoped TensorProduct
open NumberField Matrix

section General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (h : HSpace.IsIsomEmb B A ι)

theorem continuous_embA : Continuous (embA hc B A ι h) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const))

theorem embA_ratA (γ : GRat hc B) : embA hc B A ι h (ratA hc B γ) = ratA hc A (embRat hc B A ι h γ) := by
  refine Subtype.ext (Units.ext ?_)
  show 1 + (embMat B A ι).map (inclR (F := F) (AF F)) *
      (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E).map (inclR (F := F) (AF F)) - 1) *
        (projMat hc B A ι).map (inclR (F := F) (AF F)) =
    (1 + embMat B A ι * (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E) - 1) *
      projMat hc B A ι).map (inclR (F := F) (AF F))
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_embHom (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι, continuous_embA D.sp.cm B A ι hι,
    fun h g => GlobalTheory.AutFunCompare.embRel_iff A B ι hι g h, ?_⟩
  rw [GlobalTheory.AutFunCompare.GQ_eq, GlobalTheory.AutFunCompare.GQ_eq]
  rintro _ ⟨γ, rfl⟩
  exact ⟨_, (embA_ratA D.sp.cm B A ι hι γ).symm⟩

end GlobalTheory.Mem.UnitaryEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Ksph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_subgroup_ksph : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S :=
  fun _ V S => ⟨_, (GlobalTheory.AutFunCompare.KsphC_eq V S).symm,
    fun _ hS _ hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩⟩

end GlobalTheory.Mem.Ksph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueUnitaryTwoStepPairMeasureStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  first | exact @GlobalTheory.GaugeEx.twoStep_existsUnique | exact GlobalTheory.GaugeEx.twoStep_existsUnique | (intros; apply GlobalTheory.GaugeEx.twoStep_existsUnique <;> assumption)
end

