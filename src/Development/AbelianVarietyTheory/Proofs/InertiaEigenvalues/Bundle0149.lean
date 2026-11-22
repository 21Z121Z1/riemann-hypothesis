import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnit
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Move

variable {K : UQ} (B : InvAlg K)

theorem det_trace_ne_zero (hP : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hP
  have hk : ∀ k : Fin (Module.finrank K.E B.A),
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * ∑ l, v l • e l) = 0 := by
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ w : B.A, Algebra.trace K.E B.A ((∑ l, v l • e l) * w) = 0 := by
    intro w
    rw [← b.sum_repr w, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hb k, mul_comm, hk k, smul_zero]
  have hz0 : ∑ l, v l • e l = 0 :=
    (Sandwich.traceForm_nondegenerate B hP).1 _ (fun w => by rw [Algebra.traceForm_apply]; exact hall w)
  apply hv
  apply e.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, hz0, map_zero]

theorem mem_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (z : B.A) :
    z ∈ mulLat K.O (y : B.A) M ↔ ((y⁻¹ : B.Aˣ) : B.A) * z ∈ M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_inv (M : Submodule K.O B.A) (y : B.Aˣ) :
    mulLat K.O ((y⁻¹ : B.Aˣ) : B.A) (mulLat K.O (y : B.A) M) = M := by
  ext z
  rw [mem_mulLat, mem_mulLat, inv_inv, Units.inv_mul_cancel_left]

theorem mulLat_mem_Lin (y : B.Aˣ) (hy : B.σ (y : B.A) = y) (M : Submodule K.O B.A) (hM : M ∈ B.Lin) :
    mulLat K.O (y : B.A) M ∈ B.Lin := by
  obtain ⟨⟨hfg, hsp⟩, hg, hσ⟩ := hM
  have hyi : B.σ ((y⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((y⁻¹ : B.Aˣ) : B.A) = B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  refine ⟨⟨hfg.map _, ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ((mulLat K.O (y : B.A) M : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (y : B.A)) '' (M : Set B.A) := by
      rw [mulLat, Submodule.map_coe]
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    exact ⟨((y⁻¹ : B.Aˣ) : B.A) * x, by simp⟩
  · rw [mem_mulLat] at hz ⊢
    rw [mul_left_comm]
    exact hg _ hz
  · rw [mem_mulLat] at hz ⊢
    have := hσ _ hz
    rwa [map_mul, hyi] at this

theorem sgnLat_mulLat (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by
  classical
  obtain ⟨e, he, -⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B M hM hσ
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (y : B.A))
    (LinearMap.mulLeft K.E ((y⁻¹ : B.Aˣ) : B.A)) (by ext x; simp) (by ext x; simp)
  let e' := e.map f
  have he' : ∀ l, e' l = (y : B.A) * e l := fun l => rfl
  have hspan : mulLat K.O (y : B.A) M = Submodule.span K.O (Set.range e') := by
    rw [← he, mulLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hN : Algebra.norm K.E (y : B.A) ≠ 0 := (y.isUnit.map (Algebra.norm K.E)).ne_zero
  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e' l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) * Algebra.leftMulMatrix e (y : B.A) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [he' l]
    conv_lhs => rw [← e.sum_repr ((y : B.A) * e l)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [hspan, SgnBasis.sgnLat_span_basis, ← he, SgnBasis.sgnLat_span_basis, hmat, Matrix.det_mul,
    ← Algebra.norm_eq_matrix_det, Desc.eta_mul (det_trace_ne_zero B hP e) hN, mul_comm]

theorem inDual_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (t : B.A) :
    InDual B t (mulLat K.O (y : B.A) M) ↔ InDual B ((y : B.A) * t) M := by
  unfold InDual
  constructor
  · intro h z hz
    have := h ((y : B.A) * z) (by rw [mem_mulLat, Units.inv_mul_cancel_left]; exact hz)
    have e : t * ((y : B.A) * z) = (y : B.A) * t * z := by ring
    rwa [e] at this
  · intro h z hz
    rw [mem_mulLat] at hz
    have := h _ hz
    have e : (y : B.A) * t * (((y⁻¹ : B.Aˣ) : B.A) * z) = t * z := by
      rw [mul_comm (y : B.A) t, mul_assoc, Units.mul_inv_cancel_left]
    rwa [e] at this

theorem term_mulLat {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by
  classical
  unfold term dlt
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indM
    have e : ((y⁻¹ : B.Aˣ) : B.A) * ((∏ j ∈ J, π j) * ((y : B.A) * u)) = (∏ j ∈ J, π j) * u := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    simp only [mem_mulLat, e]
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indD
    have e : (y : B.A) * ((∏ j ∈ J, π j) * s) = (∏ j ∈ J, π j) * ((y : B.A) * s) := by ring
    simp only [inDual_mulLat, e]

theorem HH_mul_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A),
    B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  intro K B ι π I I' u s y hB hy
  obtain ⟨⟨yu, rfl⟩, hσ⟩ := hy
  have hσ' : B.σ ((yu⁻¹ : B.Aˣ) : B.A) = ((yu⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) = 1 := by
      conv_lhs => rw [← hσ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((yu⁻¹ : B.Aˣ) : B.A) = B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) * ((yu⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  unfold HH
  rw [mul_finsum_mem]
  symm
  refine finsum_mem_eq_of_bijOn (fun M => mulLat K.O (yu : B.A) M) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun M => mulLat K.O ((yu⁻¹ : B.Aˣ) : B.A) M) ⟨fun M _ => ?_, fun M _ => ?_⟩
      (fun M hM => mulLat_mem_Lin B yu hσ M hM) (fun M hM => ?_)
    · exact mulLat_inv B M yu
    · have := mulLat_inv B M yu⁻¹
      rwa [inv_inv] at this
    · have := mulLat_mem_Lin B yu⁻¹ hσ' M hM
      exact this
  · intro M hM
    rw [sgnLat_mulLat B hB.2 M hM.1 hM.2.2 yu, term_mulLat]
    ring

end GlobalTheory.UnitLemma.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerRelIndexIntUnitsNeZeroStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero | exact GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero | (intros; apply GlobalTheory.UnitLemma.StabIdx.stabilizer_relIndex_intUnits_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectors
section
open GlobalTheory.MeetsGen

noncomputable section
namespace GlobalTheory.MeetsTypeVec

theorem lift_apply_mem {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (W : Submodule K V) (hW : ∀ g x, x ∈ W → φ g x ∈ W)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ W) :
    MonoidAlgebra.lift K (Module.End K V) G φ a x ∈ W := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => by
    rw [LinearMap.smul_apply]; exact W.smul_mem _ (hW g x hx)

theorem proj_eigen {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (y : V) (u' : U) :
    φ u' (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y)
      = ((ψ u' : Kˣ) : K) • MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y := by
  have hφ : ∀ u : U, φ u' (φ u y) = φ ((u' * u : U) : G) y := by
    intro u; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp only [pU, map_sum, MonoidAlgebra.lift_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    Finset.smul_sum, hφ]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, smul_smul]
  congr 1
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : ((ψ u' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

theorem meets : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  intro K G V _ _ _ _ _ ρ U _ ψ e b he W hW0 hWs hWe
  set φ : G →* Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hφdef
  have hφ : ∀ g x, φ g x = ρ g x := fun _ _ => rfl
  have hWs' : ∀ g x, x ∈ W → φ g x ∈ W := fun g x hx => by rw [hφ]; exact hWs g x hx
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : x = ∑ g : G, φ g (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x)) := by
    conv_lhs => rw [← hWe x hxW, he]
    simp only [map_sum, map_mul, MonoidAlgebra.lift_single, one_smul, LinearMap.sum_apply, Module.End.mul_apply]
  intro hbot
  apply hx0
  rw [hsum]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hmem : MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x) ∈
      W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) := by
    refine ⟨lift_apply_mem φ W hWs' _ (lift_apply_mem φ W hWs' _ hxW), ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun u => LinearMap.mem_ker.2 ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ← hφ, proj_eigen,
      sub_self]
  rw [hbot] at hmem
  rw [(Submodule.mem_bot K).1 hmem, map_zero]

end GlobalTheory.MeetsTypeVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_descend_pair_quotient {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [TopologicalSpace M] (N : Subgroup Γ) (w : Γ × Γ → M)
    (hw : Continuous w) (h : ∀ g h : Γ, ∀ n ∈ N, ∀ n' ∈ N, w (g * n, h * n') = w (g, h)) :
    ∃ W : (Γ ⧸ N) × (Γ ⧸ N) → M, Continuous W ∧
      ∀ g h : Γ, W ((g : Γ ⧸ N), (h : Γ ⧸ N)) = w (g, h) := by
  refine ⟨fun p => Quotient.liftOn₂' p.1 p.2 (fun a b => w (a, b)) ?_, ?_, fun g h => rfl⟩
  · intro a b a' b' ha hb
    have e := h a b _ (QuotientGroup.leftRel_apply.1 ha) _ (QuotientGroup.leftRel_apply.1 hb)
    simpa using e.symm
  · rw [((QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := N))).isQuotientMap.continuous_iff]
    exact hw

theorem sum_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ ζ hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l 1 one_pos ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l 1 g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegrality
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := GlobalTheory.T.isReduced_of_lieReg' K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact GlobalTheory.T.isIntegral_residue_comap_involution_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply GlobalTheory.T.not_isIntegral_residue_inv_small_integer K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := GlobalTheory.T.exists_representatives_two_element_orbits_involution (MaximalSpectrum B.A) s hs
  refine ⟨r, (valsAt w e).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    GlobalTheory.T.zValuationsAtIndices_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedIntegralEqVolMulOrbitalIntegralStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  first | exact @GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | exact GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | (intros; apply GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem units_adicCompletion_hom_ext (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B)
    (hf : IsOpen (f.ker : Set (v.adicCompletion F)ˣ))
    (hg : IsOpen (g.ker : Set (v.adicCompletion F)ˣ))
    (hc : ∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) =
      g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) :
    ∀ x, f x = g x := by
  intro x
  set S : Set (v.adicCompletion F)ˣ :=
    (fun y => x⁻¹ * y) ⁻¹' ((f.ker : Set (v.adicCompletion F)ˣ) ∩ g.ker) with hS
  have hSo : IsOpen S := (hf.inter hg).preimage (continuous_const.mul continuous_id)
  have hxS : x ∈ S := by simp [hS, MonoidHom.mem_ker]
  obtain ⟨U, hU, hUS⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hSo
  have hxU : (x : v.adicCompletion F) ∈ U := by
    rw [← hUS] at hxS; exact hxS
  have hU0 : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open
    hU0 ⟨x, hxU, by simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hk.2 (by simp)
  set c : Fˣ := Units.mk0 k hk0
  have hcS : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c ∈ S := by
    rw [← hUS]; simpa [c] using hk.1
  simp only [hS, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    map_mul, map_inv] at hcS
  have h1 : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = f x := by
    have := hcS.1; rw [inv_mul_eq_one] at this; exact this.symm
  have h2 : g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g x := by
    have := hcS.2; rw [inv_mul_eq_one] at this; exact this.symm
  rw [← h1, ← h2, hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNormStatement
section
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_norm_trace_surjective : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex K L = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  first | exact @GlobalTheory.unramified_quadratic_uniformizer_trace_norm | exact GlobalTheory.unramified_quadratic_uniformizer_trace_norm | (intros; apply GlobalTheory.unramified_quadratic_uniformizer_trace_norm <;> assumption)
end

