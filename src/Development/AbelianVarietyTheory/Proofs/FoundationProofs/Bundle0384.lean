import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0376
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0380
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompactStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperTriangular_conj_integral_compact : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (E : IntermediateField ℚ_[l] (Qbar l)) (r : Γ →* GL (Fin 2) (Qbar l)), FiniteDimensional ℚ_[l] E → Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E) → ∃ B : GL (Fin 2) (Qbar l), (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 ∧ ∀ g i j, ((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E ∧ ‖((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | exact GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | (intros; apply GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  intro l _ Ω _ _ _ e S A W hW a ha
  set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT
  have hTc : IsClosed (T : Set (G ℚ Ω)) := by
    have h1 : IsClosed (W.ker : Set (G ℚ Ω)) := isClosed_singleton.preimage hW.cont
    have h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω)) := isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)
    exact h1.inter h2
  have hNS : NS Ω (S : Set Pl) ≤ T := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hTc
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    refine ⟨hW.unr v hv B hB hτ, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hW.above v h)
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ
  have haT : a ∈ T := hNS ((QuotientGroup.eq_one_iff _).mp ha)
  have hWa : W a = 1 := haT.1
  have hca : cycZ ℚ Ω l a = 1 := haT.2
  have hcb : cycBar ℚ Ω l a = 1 := by simp [cycBar, hca]
  have hdt : dt W a = 1 := by simp [dt, hWa]
  apply Units.ext
  rw [dual1, tw_val]
  simp [hcb, hdt, hWa]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro l _ Ω _ _ _ e S A W hW c hc s i j

  have hdet : (mat W s).det ∈ c.O := by
    let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W s i j, hc s i j⟩
    have hM : M.map c.O.val = mat W s := by ext i j; rfl
    have h := RingHom.map_det (SubringClass.subtype c.O) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← hM]
    have e1 : (M.map c.O.val) = M.map (SubringClass.subtype c.O) := rfl
    rw [e1, ← h]
    exact (M.det).2

  have hinv : (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    have h2 : dt W s ^ 2 = 1 := by
      have := congrArg (fun f => f s) hW.det2
      simpa using this
    have : (dt W s)⁻¹ = dt W s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
    rw [this]; rfl
  have hcyc : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) ∈ c.O := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O
    exact c.O.algebraMap_mem _
  have hval : mat (dual1 W) s i j = ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s i j := by
    simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]
  rw [hval, hinv]
  exact c.O.mul_mem (c.O.mul_mem hcyc hdet) (hc s i j)

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_upperTriangular_decompGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  intro l _ Ω _ _ _ e S A W hW s hs
  have h := hW.upper s hs
  simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_zero]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernelStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  first | exact @GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | exact GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | (intros; apply GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m → (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) → Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  first | exact @GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | exact GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | (intros; apply GlobalTheory.hasWeight_neg_of_pow_cyc_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvarianceStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_commutator_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  first | exact @GlobalTheory.Ord2.ht_commutator | exact GlobalTheory.Ord2.ht_commutator | (intros; apply GlobalTheory.Ord2.ht_commutator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecompositionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (M : Type) [AddCommGroup M] (u : G ℚ Ω → M), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → (∀ x : M, l ^ n • x = 0) → IsLocallyConstant (fun s : Ine (F := ℚ) B => u s) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, u (s * t) = u s + u t) → ∀ g ∈ Dec (F := ℚ) B, ∀ s ∈ Ine (F := ℚ) B, u (g * s * g⁻¹) = u s := by
  first | exact @GlobalTheory.TameConjInv.conj_invariant | exact GlobalTheory.TameConjInv.conj_invariant | (intros; apply GlobalTheory.TameConjInv.conj_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

variable {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

def zcl {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : H2 (charRep μ) :=
  Submodule.Quotient.mk ⟨zc c n S ξ i, zc_mem hμ hξ i⟩

theorem res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ) (i : Ix c) :
    resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0 := by
  obtain ⟨u, hu, huO, hcu⟩ := hcob
  unfold zcl resH2
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  refine ⟨fun g => crd c n i (u g), continuous_crd hu.domRestrict (fun g => huO _) n i, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply, restrictCocycles2_apply]
  change _ = zc c n S ξ i (((g : G ℚ Ω) : GS Ω (S : Set Pl)), ((h : G ℚ Ω) : GS Ω (S : Set Pl)))
  rw [zc_mk hξ, MonoidHom.coe_comp, Function.comp_apply, charRep_apply]
  have hμg : ((μ (locFam S Av v g) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l g : ℤ_[l]) :=
    congrArg Units.val (DFunLike.congr_fun hμ (g : G ℚ Ω))
  rw [hμg]
  have hc := (cg_iff (hξ.int g h) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g))).1
    (hcu g g.2 h h.2) i
  rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g),
    crd_sub i (algebraMap_mul_mem _ (huO h)) (huO _), crd_algebraMap_mul i _ (huO h)] at hc
  rw [hc]; rfl

theorem cob_of_res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (h0 : ∀ i, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0) :
    Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
  have hb : ∀ i, ∃ ci : Dec (F := ℚ) (Av v) → ZMod (l ^ n), Continuous ci ∧
      d1 ((charRep μ).comp (locFam S Av v)) ci =
        fun p => zc c n S ξ i (((p.1 : G ℚ Ω) : GS Ω (S : Set Pl)), ((p.2 : G ℚ Ω) : GS Ω (S : Set Pl))) := by
    intro i
    have := h0 i
    unfold zcl resH2 at this
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      separated_dvr_second_cohomology_mem] at this
    exact this
  choose ci hci hd using hb
  classical
  refine ⟨fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.domRestrict (Dec (F := ℚ) (Av v) : Set (G ℚ Ω))
        fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0) =
        fun g => lft c n (fun i => ci i g) := by
      funext g; exact dif_pos g.2
    rw [this]
    exact Continuous.comp (g := lft c n) (f := fun g i => ci i g) continuous_of_discreteTopology
      (continuous_pi fun i => hci i)
  · intro s
    dsimp only
    split_ifs
    · exact lft_mem _ _
    · exact c.O.zero_mem
  · intro s hs t ht
    dsimp only
    rw [dif_pos ht, dif_pos ((Dec (F := ℚ) (Av v)).mul_mem hs ht), dif_pos hs]
    have hm : ∀ a, lft c n a ∈ c.O := lft_mem n
    refine (cg_iff (hξ.int s t) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _))).2
      fun i => ?_
    rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _),
      crd_sub i (algebraMap_mul_mem _ (hm _)) (hm _), crd_algebraMap_mul i _ (hm _), crd_lft, crd_lft, crd_lft]
    have e := congrFun (hd i) (⟨s, hs⟩, ⟨t, ht⟩)
    rw [zc_mk hξ, d1_apply, MonoidHom.coe_comp, Function.comp_apply, charRep_apply] at e
    have hμg : ((μ (locFam S Av v ⟨s, hs⟩) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l s : ℤ_[l]) :=
      congrArg Units.val (DFunLike.congr_fun hμ s)
    rw [hμg] at e
    rw [← e]; rfl

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

theorem reciprocity : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl),
    l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S →
    (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  intro hL l _ Ω _ _ _ c n S ξ v₀ hl hS hξ hv₀ hloc B hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, continuousOn_const, fun _ => c.O.zero_mem, fun s _ t _ => ?_⟩
    unfold Cg
    simp only [mul_zero, sub_zero, add_zero, pow_zero, norm_one]
    exact norm_le_one_of_mem (hξ.int s t)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.Published.exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, hinv, hPT⟩ := hL.pt ℚ Ω l n (Or.inl hl) hn ζ hζ
  classical
  let Av : S → ValuationSubring Ω := fun v =>
    if h : v.1 = v₀ then B else Classical.choose (hloc v.1 v.2 h)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := by
    intro v
    by_cases h : v.1 = v₀
    · simp only [Av, dif_pos h]; rw [h]; exact hB
    · simp only [Av, dif_neg h]; exact (Classical.choose_spec (hloc v.1 v.2 h)).1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  have hNT := (hPT S hS Av hAv μ hμ (ZMod (l ^ n)) (charRep μ) (contAction_charRep hμ)).1
  have hres : ∀ i, resH2 (charRep μ) (locFam S Av ⟨v₀, hv₀⟩) (continuous_locFam S Av _)
      (zcl hμ hξ i) = 0 := by
    intro i
    have hsum := hNT.sum_eq_zero (zcl hμ hξ i)
    rw [Finset.sum_eq_single ⟨v₀, hv₀⟩] at hsum
    · have hinj : Function.Injective (invAt S Av μ hμ inv ⟨v₀, hv₀⟩) :=
        (hinv _ _ (hAv ⟨v₀, hv₀⟩)).1.1.comp (toMuLoc_bijective S Av μ hμ _).1
      exact hinj (by rw [hsum, map_zero])
    · intro v _ hv
      have hne : v.1 ≠ v₀ := fun h => hv (Subtype.ext h)
      have hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
        simp only [Av, dif_neg hne]; exact (Classical.choose_spec (hloc v.1 v.2 hne)).2
      rw [res_zcl_eq_zero hμ hξ Av v hcob i, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcob := cob_of_res_zcl_eq_zero hμ hξ Av ⟨v₀, hv₀⟩ hres
  have hA : Av ⟨v₀, hv₀⟩ = B := dif_pos rfl
  rw [hA] at hcob
  exact hcob

end GlobalTheory.Ord2.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCocycleOfPadicLimitOfApproxCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.LimCoc

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  rw [h]
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [this, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem ultra3 {K : Type*} [NormedField K] [IsUltrametricDist K] (a b c e : K) (ε : ℝ)
    (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) (hc : ‖c‖ ≤ ε) (he : ‖e‖ ≤ ε) :
    ‖a + b - c - e‖ ≤ ε := by
  have hsub : ∀ u v : K, ‖u‖ ≤ ε → ‖v‖ ≤ ε → ‖u - v‖ ≤ ε := fun u v hu hv => by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by rwa [norm_neg]))
  exact hsub _ _ (hsub _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)) hc) he

theorem mulVec_small {K : Type*} [NormedField K] [IsUltrametricDist K]
    (A : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) (ε : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ ε) (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hw 0)
  have key : ∀ j, ‖A i j * w j‖ ≤ ε := fun j => by
    rw [norm_mul]
    calc ‖A i j‖ * ‖w j‖ ≤ 1 * ε := mul_le_mul (hA i j) (hw j) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key 0) (key 1))

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  intro l _ Γ _ M z y hM _ hz hy s t
  funext i
  rw [← sub_eq_zero, ← norm_eq_zero]
  have hbound : ∀ r : ℕ, ‖y (s * t) i - (y s + M s *ᵥ y t) i‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ r := by
    intro r
    rw [← norm_pow]
    have hdecomp : y (s * t) i - (y s + M s *ᵥ y t) i =
        (y (s * t) i - z r (s * t) i) + (z r (s * t) i - (z r s + M s *ᵥ z r t) i)
          - (y s i - z r s i) - (M s *ᵥ (y t - z r t)) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
      ring
    rw [hdecomp]
    exact ultra3 _ _ _ _ _ (hy r (s * t) i) (hz r s t i) (hy r s i)
      (mulVec_small (M s) (y t - z r t) _ (hM s) (fun j => by simpa using hy r t j) i)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)
  exact le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _)

end GlobalTheory.LimCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationAppr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem spLink_of_spec_approx (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l)
    (h : ∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
      ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤
        ‖((l : ℕ) : Qbar l) ^ r‖) :
    SpLink A e χ (fun r s x => Y r s x 1) y := by
  intro n
  refine ⟨n, fun r hr s hs hc => ?_⟩
  have h1 := h r s hs hc
  have heq : spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1 =
      sp (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Y r s x 1) s := by
    simp only [spec, sp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at h1
  unfold Cg
  refine h1.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) hr

end GlobalTheory.KZ
end

