import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.InvPairing

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def stab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixed_iff (σ : Representation ℂ G W) (H : Subgroup G) (v : W) :
    v ∈ GlobalTheory.PRep.fixed σ H ↔ ∀ h ∈ H, σ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem exists_fixed_avg (σ : Representation ℂ G W) (hs : GlobalTheory.PRep.IsSmooth σ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (x : W) :
    ∃ x₀ ∈ GlobalTheory.PRep.fixed σ K, ∀ ℓ : W →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ v, ℓ (σ k v) = ℓ v) → ℓ x = ℓ x₀ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hSo : IsOpen ((stab σ x : Subgroup G) : Set G) := hs x
  haveI : Finite (K ⧸ (stab σ x).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hSo.preimage continuous_subtype_val)
  let f : K ⧸ (stab σ x).subgroupOf K → W := fun q => Quotient.liftOn' q (fun k : K => σ k x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    change σ ((a : G)⁻¹ * b) x = x at hab
    show σ a x = σ b x
    calc σ a x = σ a (σ ((a : G)⁻¹ * b) x) := by rw [hab]
      _ = σ b x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hrange : Set.range f = Set.range (fun k : K => σ k x) := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H k => exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hfin : (Set.range (fun k : K => σ k x)).Finite := hrange ▸ Set.finite_range f
  set O := hfin.toFinset with hO
  have hxO : x ∈ O := by
    rw [hO, Set.Finite.mem_toFinset]
    exact ⟨1, by simp⟩
  have hperm : ∀ k ∈ K, ∑ v ∈ O, σ k v = ∑ v ∈ O, v := by
    intro k hk
    refine Finset.sum_nbij' (fun v => σ k v) (fun v => σ k⁻¹ v) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩ * j, by simp [Module.End.mul_apply]⟩
    · intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv ⊢
      obtain ⟨j, rfl⟩ := hv
      exact ⟨⟨k, hk⟩⁻¹ * j, by simp [Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  refine ⟨((O.card : ℂ))⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · rw [mem_fixed_iff]
    intro k hk
    rw [map_smul, map_sum, hperm k hk]
  · intro ℓ hℓ
    have hconst : ∀ v ∈ O, ℓ v = ℓ x := by
      intro v hv
      rw [hO, Set.Finite.mem_toFinset] at hv
      obtain ⟨j, rfl⟩ := hv
      exact hℓ j j.2 x
    have hcard : (O.card : ℂ) ≠ 0 := by
      have : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
      exact_mod_cast this.ne'
    rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem exists_rep (U : Submodule ℂ W) [FiniteDimensional ℂ U]
    (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (hB : ∀ x, x ≠ 0 → 0 < (B x x).re) (f : U →ₗ[ℂ] ℂ) :
    ∃ z : U, ∀ x : U, f x = B x z := by
  let T : U →ₗ[ℝ] Module.Dual ℂ U :=
    { toFun := fun z => (B.flip (z : W)).comp U.subtype
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro r z
        ext x
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
          Submodule.coe_smul]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r z, Submodule.coe_smul, LinearMap.map_smulₛₗ, Complex.real_smul,
          RCLike.conj_ofReal, smul_eq_mul]
        rfl }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have h1 : B z z = 0 := by
      have := LinearMap.congr_fun hz z
      simpa [T] using this
    have := hB z (fun h => hne (Subtype.ext h))
    rw [h1] at this
    simp at this
  have hrank : Module.finrank ℝ U = Module.finrank ℝ (Module.Dual ℂ U) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ U, ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ U),
      Subspace.dual_finrank_eq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  obtain ⟨z, hz⟩ := hsurj f
  exact ⟨z, fun x => by rw [← hz]; rfl⟩

end GlobalTheory.InvPairing

namespace GlobalTheory.InvPairing

theorem exists_intertwiner : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  intro G _ _ _ K hKo hKc W W' _ _ _ _ σ σ' hσ hσ' B C hB hBinv hCinv
  have huniq : ∀ z z' : W, (∀ x, B x z = B x z') → z = z' := by
    intro z z' h
    by_contra hne
    have hne' : z - z' ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hB _ hne'
    have h0 : B (z - z') (z - z') = 0 := by rw [map_sub (B (z - z')), h (z - z'), sub_self]
    rw [h0] at hpos
    simp at hpos
  have hex : ∀ y, ∃ z, ∀ x, C x y = B x z := by
    intro y
    set K' := K ⊓ stab σ' y with hK'
    have hSo : IsOpen ((stab σ' y : Subgroup G) : Set G) := hσ' y
    have hKo' : IsOpen (K' : Set G) := hKo.inter hSo
    have hKc' : IsCompact (K' : Set G) := hKc.inter_right (Subgroup.isClosed_of_isOpen _ hSo)
    haveI := hσ.2 K' hKo' hKc'
    obtain ⟨z, hz⟩ := exists_rep (GlobalTheory.PRep.fixed σ K') B hB ((C.flip y).comp (GlobalTheory.PRep.fixed σ K').subtype)
    refine ⟨z, fun x => ?_⟩
    obtain ⟨x₀, hx₀, hℓ⟩ := exists_fixed_avg σ hσ.1 K' hKc' x
    have e1 := hℓ (C.flip y) (fun k hk v => by
      have hy : σ' k y = y := (Subgroup.mem_inf.mp hk).2
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hy]
      exact hCinv k v y)
    have e2 := hℓ (B.flip z) (fun k hk v => by
      have hz' : σ k z = z := (mem_fixed_iff σ K' z).mp z.2 k hk
      simp only [LinearMap.flip_apply]
      conv_lhs => rw [← hz']
      exact hBinv k v z)
    simp only [LinearMap.flip_apply] at e1 e2
    rw [e1, e2]
    exact hz ⟨x₀, hx₀⟩
  choose φ₀ hφ₀ using hex
  refine ⟨{ toFun := φ₀, map_add' := ?_, map_smul' := ?_ }, ?_, fun x y => hφ₀ y x⟩
  · intro a b
    apply huniq
    intro x
    rw [map_add (B x), ← hφ₀, ← hφ₀, ← hφ₀, map_add]
  · intro c a
    apply huniq
    intro x
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ (B x), ← hφ₀, ← hφ₀, LinearMap.map_smulₛₗ]
  · intro g y
    apply huniq
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hφ₀]
    have hx : x = σ g (σ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx, hCinv, hBinv]
    exact hφ₀ y _

end GlobalTheory.InvPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPowArchProjNotMemOfEigenvalueTwo
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Twist

open scoped TensorProduct Matrix

set_option maxHeartbeats 1600000 in

theorem exists_pow_projArch_not_mem_of_eigen_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  intro D V g x hx hg w K hK
  classical
  set c : Fin V.rank → D.host.E := ⇑(V.frame.repr x) with hc_def
  have hM : (g.1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) • c := by
    have h1 := congrArg (fun y => ⇑(V.frame.repr y)) hg
    simp only [GlobalTheory.Cusp.ratAct, map_smul, Finsupp.coe_smul] at h1
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, LinearMap.toMatrix_toLin] at h1
    exact h1
  have hMn : ∀ n : ℕ, ((g ^ n).1.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ c = (2 : D.host.E) ^ n • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    have : V.frame.repr x = 0 := Finsupp.ext h
    simpa using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual D.host.F D.host.E, φ (c j) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hj ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)

  let ι : D.host.E →+* w.Completion ⊗[D.host.F] D.host.E := inclR (F := D.host.F) w.Completion
  let Λ : w.Completion ⊗[D.host.F] D.host.E →ₗ[w.Completion] w.Completion :=
    (TensorProduct.AlgebraTensorModule.rid D.host.F w.Completion w.Completion).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map LinearMap.id φ
  have hΛ1 : ∀ e : D.host.E, Λ (ι e) = algebraMap D.host.F w.Completion (φ e) := by
    intro e
    simp [Λ, ι, inclR, Algebra.algebraMap_eq_smul_one]
  have : IsModuleTopology w.Completion (w.Completion ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (w.Completion ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing w.Completion _
  have hΛ : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  let f : GArch D.sp.cm.sig V.gram w → w.Completion := fun h =>
    Λ (((matHom _ D.sp.cm.sig V.gram h).val *ᵥ (fun i => ι (c i))) j)
  have hm : Continuous fun h : GArch D.sp.cm.sig V.gram w =>
      (matHom _ D.sp.cm.sig V.gram h).val :=
    Units.continuous_val.comp (isEmbedding_matHom _ _ _).continuous
  have hf : Continuous f := hΛ.comp ((continuous_apply j).comp (hm.matrix_mulVec continuous_const))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have he : ∀ γ : GF V, (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w γ)).val = (γ.1.1).map ι :=
    fun γ => rfl
  have hval : ∀ n : ℕ, f (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V)) =
      algebraMap D.host.F w.Completion ((2 : D.host.F) ^ n * φ (c j)) := by
    intro n
    have e1 : (matHom _ D.sp.cm.sig V.gram (ratArch D.sp.cm.sig V.gram w (g ^ n : GF V))).val = ((g ^ n).1.1).map ι := he (g ^ n)
    simp only [f]
    rw [e1, show (fun i => ι (c i)) = ⇑ι ∘ c from rfl, ← RingHom.map_mulVec, hMn n, Pi.smul_apply, smul_eq_mul, hΛ1]
    congr 1
    rw [show (2 : D.host.E) ^ n * c j = ((2 : D.host.F) ^ n) • c j by rw [Algebra.smul_def, map_pow, map_ofNat],
      map_smul, smul_eq_mul]
  have hnorm : ∀ a : D.host.F, ‖algebraMap D.host.F w.Completion a‖ = w a := fun a => by
    rw [show algebraMap D.host.F w.Completion a = ((a : D.host.F) : w.Completion) from rfl]
    simp only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]
    rfl
  have hpos : 0 < w (φ (c j)) := (InfinitePlace.pos_iff).2 hφ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / w (φ (c j))) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun hmem => ?_⟩
  rw [show projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) = ratArch D.sp.cm.sig V.gram w (g ^ n : GF V) from
    projArch_ratEmb _ _ w _] at hmem
  have h1 := hC _ hmem
  rw [hval, hnorm, map_mul, map_pow] at h1
  have h2 : w (2 : D.host.F) = 2 := by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
  rw [h2] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalUnitaryScalingWittFrame
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial
open Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped Classical

noncomputable section

namespace GlobalTheory.TrScale

theorem exists_scale (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) : ∃ g : GF V, (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x) ∧ (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E)⁻¹ • x) ∧ ∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z := by
  let b : Fin (wittIndex V) × Bool → V.V := fun a => if a.2 then Φ.e a.1 else Φ.f a.1
  let σ : D.host.E →+* D.host.E := D.sp.cm.sig
  let d : Fin (wittIndex V) × Bool → D.host.E := fun a =>
    if u a.1 = 0 then 1 else if (u a.1 = 1 ↔ a.2 = true) then 2 else 2⁻¹
  have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have hσd : ∀ i s, σ (d (i, s)) * d (i, !s) = 1 := fun i s => by
    simp only [d]
    split_ifs <;> cases s <;> simp_all [map_inv₀, hσ2, h2]
  let S : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E :=
    (1 : Matrix _ _ D.host.E).submatrix id ((Equiv.refl _).prodCongr Equiv.boolNot)
  have fe : ∀ i j, V.hT (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := fun i j => (Φ.ef j i).trans (by simp only [eq_comm])
  have ef : ∀ i j, V.hT (Φ.e i) (Φ.f j) = if i = j then 1 else 0 := fun i j => by
    rw [← V.herm.eq, fe]; by_cases h : i = j <;> simp [h, eq_comm]
  have ee : ∀ i j, V.hT (Φ.e i) (Φ.e j) = 0 := fun i j => Φ.ee j i
  have ff : ∀ i j, V.hT (Φ.f i) (Φ.f j) = 0 := fun i j => Φ.ff j i
  have hB : cT σ (cols V b) * V.gram * cols V b = S := by
    rw [gram_cols]
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [b, S, ee, ff, ef, fe, Matrix.one_apply]
  have hSS : S * S = 1 := by
    refine (Matrix.mul_submatrix_one (Equiv.refl _) _ S).trans ?_
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [S, Matrix.one_apply]
  have hS : cT σ S = S := by
    ext ⟨i, _ | _⟩ ⟨j, _ | _⟩ <;> simp [cT, S, Matrix.one_apply, eq_comm, apply_ite σ]
  let P : Matrix (Fin (wittIndex V) × Bool) (Fin (wittIndex V) × Bool) D.host.E := diagonal d
  have hP : cT σ P * S * P = S := by
    have hc : cT σ P = diagonal fun a => σ (d a) := by
      ext a c; by_cases h : a = c <;> simp [cT, P, diagonal_apply, h, eq_comm]
    rw [hc]
    ext ⟨i, s⟩ ⟨j, t⟩
    simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul, S, submatrix_apply, Matrix.one_apply, id, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, Prod.mk.injEq, Equiv.boolNot_apply]
    by_cases hij : i = j
    · subst hij
      cases s <;> cases t <;> simp only [true_and, and_true, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, and_self, mul_one, mul_zero, zero_mul, and_false, ite_true, ite_false, Prod.mk.injEq]
      all_goals first | exact hσd i _ | exact congrArg _ (hσd i _) | skip
    · simp [hij]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = S * (cT σ (cols V b) * V.gram) := ⟨_, rfl⟩
  have hQB : Q * cols V b = 1 := by rw [hQ, Matrix.mul_assoc, hB, hSS]
  have h1 : cT σ (cols V b) * V.gram = S * Q := by rw [hQ, ← Matrix.mul_assoc S S, hSS, Matrix.one_mul]
  have h2' : V.gram * cols V b = cT σ Q * S := by
    have := congrArg (cT σ) h1
    rwa [cT_mul, cT_mul, AutFunCompare.cT_cT', IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_gram, hS] at this
  have hw := unitary_extension σ h1 h2' hQB hP
  have hi : V.gram⁻¹ * (cT σ (1 + cols V b * (P - 1) * Q) * V.gram) * (1 + cols V b * (P - 1) * Q) = 1 := by
    rw [Matrix.mul_assoc, hw, Matrix.nonsing_inv_mul _ (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V)]
  let w : GF V := ⟨⟨_, _, mul_eq_one_comm.1 hi, hi⟩, hw⟩
  have act : ∀ {p : Type} (x y : p → V.V), (1 + cols V b * (P - 1) * Q) * cols V x = cols V y →
      ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (x a) = y a := fun x y h a => by
    refine V.frame.repr.injective (DFunLike.coe_injective ?_)
    rw [GlobalTheory.Cusp.ratAct, Matrix.repr_toLin]
    exact funext fun i => congrFun (congrFun h i) a
  have hwb : ∀ a, GlobalTheory.Cusp.ratAct D.sp.cm V w (b a) = d a • b a := act b (fun a => d a • b a) (by
    rw [Matrix.add_mul, Matrix.mul_assoc, hQB, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]
    ext r a; simp [cols, P, Matrix.mul_diagonal, mul_comm])
  refine ⟨w, fun x hx => ?_, fun x hx => ?_, fun z hz1 hz2 => ?_⟩
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E) • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · refine (Submodule.span_le (p := LinearMap.eqLocus (GlobalTheory.Cusp.ratAct D.sp.cm V w) ((2 : D.host.E)⁻¹ • LinearMap.id))).2 ?_ hx
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_eq_iff_eq_neg] at hi
    · have := hwb (i, true); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
    · have := hwb (i, false); simp only [b, d, hi] at this; simpa [LinearMap.mem_eqLocus] using this
  · have hz : ∀ a, u a.1 ≠ 0 → V.hT (b a) z = 0 := by
      rintro ⟨i, s⟩ h
      have hm1 : ∀ x, x ∈ Φ.sub u ∨ x ∈ Φ.sub (-u) → V.hT x z = 0 := fun x hx => hx.elim (hz1 x) (hz2 x)
      apply hm1
      rcases (show u i = 1 ∨ u i = -1 by generalize u i = t at h; revert t; decide) with h' | h' <;> cases s <;>
        simp only [b, if_true, if_false, Bool.false_eq_true]
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, by simp [h'], rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, h', rfl⟩))
      · exact .inl (by rw [WittFrame.sub]; exact Submodule.subset_span (.inr ⟨i, h', rfl⟩))
      · exact .inr (by rw [WittFrame.sub]; exact Submodule.subset_span (.inl ⟨i, by simp [h'], rfl⟩))
    have hY : Q * cols V (fun _ : Unit => z) = S * of fun a (_ : Unit) => V.hT (b a) z := by
      rw [hQ, Matrix.mul_assoc, gram_cols]
    have hSY : S * of (fun a (_ : Unit) => V.hT (b a) z) = of fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z := by
      simp only [S]; rw [Matrix.one_submatrix_mul]
      ext ⟨i, s⟩ c; rfl
    have hZ : (P - 1) * of (fun (a : Fin (wittIndex V) × Bool) (_ : Unit) => V.hT (b (a.1, !a.2)) z) = 0 := by
      ext ⟨i, s⟩ c
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, show P = diagonal d from rfl, Matrix.diagonal_mul, of_apply,
        Matrix.zero_apply]
      by_cases hu : u i = 0
      · simp [d, hu]
      · rw [hz (i, !s) hu]; simp
    have key : (1 + cols V b * (P - 1) * Q) * cols V (fun _ : Unit => z) = cols V (fun _ : Unit => z) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hY, hSY, hZ, Matrix.mul_zero, add_zero]
    exact act (fun _ : Unit => z) (fun _ => z) key ()

end GlobalTheory.TrScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicUnitaryPointExtLocalComponents
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.TrFinExt

private theorem eq_of_finE_map_prV_eq_forall_place {D : D7} (V : HSp D) (a b : GA D V)
    (h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V a).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V b).val.map (Formalism.UG.prV (E := D.host.E) u))
    (i j : Fin V.rank) :
    (Formalism.IndefR.Lev.finE V a).val i j = (Formalism.IndefR.Lev.finE V b).val i j := by

  rw [← sub_eq_zero]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  rw [Matrix.map_apply, Matrix.map_apply] at hw
  rw [map_sub, hw, sub_self]

theorem gfc_ext : ∀ {D : D7} (V : HSp D) (x y : GfC V), (∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V (x : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V (y : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u)) → x = y := by
  intro D V x y h

  have hx : infHom V (x : GA D V) = 1 := x.2
  have hy : infHom V (y : GA D V) = 1 := y.2
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply GlobalTheory.FinIsoGrp.proj_inj D
  · have ex := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hx
    have ey := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => g.val i j) hy
    exact ex.trans ey.symm
  · have e := eq_of_finE_map_prV_eq_forall_place V (x : GA D V) (y : GA D V) h i j
    rw [GlobalTheory.FinIsoGrp.finE_val, GlobalTheory.FinIsoGrp.finE_val] at e
    exact e

end GlobalTheory.TrFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  first | exact @GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | exact GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | (intros; apply GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionFinitePlaceLatticeVacuaScalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_compression_finite_place_lattice_vacua_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (w : WO S T), ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inl v) w) f) = γ * ipO μ 𝓕 g f := by
  first | exact @GlobalTheory.PlaceCompress.compress_fin | exact GlobalTheory.PlaceCompress.compress_fin | (intros; apply GlobalTheory.PlaceCompress.compress_fin <;> assumption)
end

