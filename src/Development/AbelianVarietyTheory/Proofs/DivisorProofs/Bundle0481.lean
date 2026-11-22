import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFifth
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.EigenPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem natMul_mem_orderC (c : Ideal (OF E)) (z : 𝓞 E) :
    ((Ideal.absNorm c : ℕ) : E) * (z : E) ∈ orderC c := by
  refine mem_orderC.2 ⟨0, ((Ideal.absNorm c : ℕ) : 𝓞 E) * z, ?_, ?_⟩
  · refine Ideal.mul_mem_right z _ ?_
    have h := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) (Ideal.absNorm_mem c)
    simpa using h
  · simp

theorem exists_sep {K : Type} [Field K] [CharZero K] (c : Ideal (OF E)) (hc : c ≠ ⊥) (σ σ' : E →+* K)
    (h : σ' ≠ bar σ) : ∃ a b : orderC c, (b : E) = IsCMField.complexConj E a ∧ σ a ≠ σ' b := by
  by_contra hn
  push_neg at hn
  have hm : ((Ideal.absNorm c : ℕ) : K) ≠ 0 := by
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.1 hc)
  have hz : ∀ z : 𝓞 E, σ (z : E) = σ' (IsCMField.complexConj E (z : E)) := by
    intro z
    have h1 := hn ⟨_, natMul_mem_orderC c z⟩
      ⟨_, natMul_mem_orderC c (IsCMField.ringOfIntegersComplexConj E z)⟩
      (by simp [IsCMField.coe_ringOfIntegersComplexConj])
    simp only [map_mul, map_natCast, IsCMField.coe_ringOfIntegersComplexConj] at h1
    exact mul_left_cancel₀ hm h1
  have heq : σ = bar σ' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_
    ext z
    exact hz z
  apply h
  rw [heq]
  ext x
  simp [bar, IsCMField.complexConj_apply_apply]

theorem adj_baseChange {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H]
    [Module O H] (B : LinearMap.BilinForm O H) (f g : Module.End O H) (hfg : ∀ h h', B (f h) h' = B h (g h'))
    (x y : K ⊗[O] H) : B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s h =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t h' => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hfg]

end GlobalTheory.EigenPair

theorem GlobalTheory.EigenPair.pairing_eig_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ σ' hne x hx y hy
  haveI : CharZero K := by
    refine ⟨fun m n hmn => ?_⟩
    rw [← map_natCast (algebraMap O K), ← map_natCast (algebraMap O K) n] at hmn
    exact Nat.cast_injective (IsFractionRing.injective O K hmn)
  obtain ⟨a, b, hab, hsep⟩ := GlobalTheory.EigenPair.exists_sep c hc σ σ' hne
  have hadj := hL.2.2.2.2.2.2.2.2 a b hab
  have hxa : (ρ a).baseChange K x = σ a • x :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)
  have hyb : (ρ b).baseChange K y = σ' b • y :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy b)
  have key := GlobalTheory.EigenPair.adj_baseChange B (ρ a) (ρ b) hadj x y
  rw [hxa, hyb, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul] at key
  have h2 : (σ a - σ' b) * B.baseChange K x y = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hsep)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFourth
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Div.cm_type_period_integral_fourth

theorem exists_smul_mem_of_tmul_mem_baseChange {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {H : Type} [AddCommGroup H] [Module O H] (Fil : Submodule O H) (h : H)
    (hh : (1 : K) ⊗ₜ[O] h ∈ Fil.baseChange K) : ∃ d : O, d ≠ 0 ∧ d • h ∈ Fil := by
  have key : ∀ x ∈ Fil.baseChange K, ∃ s : O, s ≠ 0 ∧ ∃ f ∈ Fil, algebraMap O K s • x = (1 : K) ⊗ₜ[O] f := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      exact ⟨1, one_ne_zero, f, hf, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, Fil.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨t, ht, g, hg, e'⟩ := ihy
      refine ⟨s * t, mul_ne_zero hs ht, t • f + s • g, Fil.add_mem (Fil.smul_mem _ hf) (Fil.smul_mem _ hg), ?_⟩
      simp only [map_mul, smul_add, mul_smul]
      rw [smul_comm (algebraMap O K s) (algebraMap O K t) x, e, e', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul, algebraMap_smul, algebraMap_smul]
    | smul k x _ ihx =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
      have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
      refine ⟨b * s, mul_ne_zero hb hs, a • f, Fil.smul_mem _ hf, ?_⟩
      rw [← mul_smul, map_mul, mul_assoc, mul_comm (algebraMap O K s), ← mul_assoc,
        mul_comm (algebraMap O K (b : O)), IsLocalization.mk'_spec, mul_smul, e, TensorProduct.tmul_smul,
        algebraMap_smul]
  obtain ⟨s, hs, f, hf, e⟩ := key _ hh
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  have h0 : TensorProduct.mk O K H 1 (s • h - f) = 0 := by
    rw [map_sub, map_smul, TensorProduct.mk_apply, TensorProduct.mk_apply, ← algebraMap_smul K, e, sub_self]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0
  refine ⟨(t : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero t.2) hs, ?_⟩
  have : (t : O) • (s • h) = (t : O) • f := by
    rw [Submonoid.smul_def, smul_sub, sub_eq_zero] at ht
    exact ht
  rw [mul_smul, this]
  exact Fil.smul_mem _ hf

theorem fil_inf_eigLat_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL i
  refine inf_eq_right.2 fun h hh => ?_
  obtain ⟨-, -, -, -, hsat, hbc, -⟩ := hL
  have h1 : inK K H h ∈ Fil.baseChange K := by
    rw [hbc]
    exact le_iSup (fun j => eigK ρ (φ j)) i hh
  obtain ⟨d, hd, hdh⟩ := exists_smul_mem_of_tmul_mem_baseChange Fil h h1
  exact hsat d h hd hdh

end GlobalTheory.Div.cm_type_period_integral_fourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem sat (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : IsSat (eigLat ρ σ) := by
  intro x h hx hxh
  have hK : (algebraMap O K x) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  show inK K H h ∈ eigK ρ σ
  have h1 : inK K H (x • h) ∈ eigK ρ σ := hxh
  rw [map_smul, ← algebraMap_smul K] at h1
  have := (eigK ρ σ).smul_mem (algebraMap O K x)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hK, one_smul] at this

theorem exists_ne_mem (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (h1 : Module.finrank K (eigK ρ σ) = 1) :
    ∃ g : H, g ≠ 0 ∧ g ∈ eigLat ρ σ := by
  have : Nontrivial (eigK ρ σ) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨⟨v, hv⟩, hv0⟩ := _root_.exists_ne (0 : eigK ρ σ)
  have hv0' : v ≠ 0 := fun h => hv0 (by ext; simp [h])
  haveI : IsLocalizedModule (nonZeroDivisors O) (inK K H) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K (inK K H)).2 (TensorProduct.isBaseChange O H K)
  obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (inK K H) v
  have hsK : algebraMap O K (s : O) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero s.2)
  have hs' : inK K H h = algebraMap O K (s : O) • v := by
    simp only at hs; rw [← hs, Submonoid.smul_def, algebraMap_smul]
  refine ⟨h, ?_, ?_⟩
  · intro h0; rw [h0, map_zero] at hs'; exact (smul_ne_zero hsK hv0') hs'.symm
  · show inK K H h ∈ eigK ρ σ
    rw [hs']; exact (eigK ρ σ).smul_mem _ hv

theorem finrank_le [Module.Free O H] [Module.Finite O H] (ρ : orderC c →+* Module.End O H) (σ : E →+* K)
    (h1 : Module.finrank K (eigK ρ σ) = 1) : Module.finrank O (eigLat ρ σ) ≤ 1 := by
  haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)
  haveI : Module.Finite K (eigK ρ σ) := Module.finite_of_finrank_eq_succ h1
  set N := eigLat ρ σ
  have hinj : Function.Injective (N.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hmem : ∀ z, N.subtype.baseChange K z ∈ eigK ρ σ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k n =>
      rw [LinearMap.baseChange_tmul]
      have hn : inK K H (n : H) ∈ eigK ρ σ := n.2
      have : k ⊗ₜ[O] (N.subtype n) = k • inK K H (n : H) := by
        simp [inK, TensorProduct.smul_tmul']
      rw [this]; exact (eigK ρ σ).smul_mem k hn
    | add x y hx hy => rw [map_add]; exact (eigK ρ σ).add_mem hx hy
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (N.subtype.baseChange K).codRestrict (eigK ρ σ) hmem)
    (fun a b hab => hinj (by simpa using congrArg Subtype.val hab))
  rw [Module.finrank_baseChange, h1] at hle
  exact hle

theorem compl [Module.Finite O H] (N : Submodule O H) (hN : IsSat N) : ∃ C : Submodule O H, IsCompl N C := by
  haveI : Module.IsTorsionFree O (H ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨h, rfl⟩ := N.mkQ_surjective m
      rw [← map_smul] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrm ⊢
      exact hN r h hr hrm
  haveI : Module.Free O (H ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  let f : H →ₗ[O] N := LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) (by
    intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hs' (N.mkQ h)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self])
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj (f := f) ?_⟩
  intro x
  ext
  simp [f, (Submodule.Quotient.mk_eq_zero N).2 x.2]
end GlobalTheory.EigenLattice

theorem GlobalTheory.EigenLattice.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ
  obtain ⟨hfree, hfin, -, hline, -⟩ := hL
  haveI := hfree; haveI := hfin
  have hsat := GlobalTheory.EigenLattice.sat (K := K) ρ σ
  obtain ⟨g0, hg0, hg0m⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ σ (hline σ)
  set N := eigLat ρ σ
  have hle := GlobalTheory.EigenLattice.finrank_le ρ σ (hline σ)
  haveI : Nontrivial N := ⟨⟨⟨g0, hg0m⟩, 0, fun h => hg0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank O N := Module.finrank_pos_iff.2 inferInstance
  have h1 : Module.finrank O N = 1 := le_antisymm hle hpos
  let b := Module.finBasisOfFinrankEq O N h1
  refine ⟨hsat, ⟨(b 0 : H), fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩, inferInstance, h1,
    GlobalTheory.EigenLattice.compl N hsat⟩
  apply le_antisymm
  · intro x hx
    have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [Submodule.span_singleton_le_iff_mem]; exact (b 0).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.EigenLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]

def tensAct (ρ : orderC c →+* Module.End O H) : orderC c ⊗[ℤ] O →ₗ[ℤ] Module.End O H :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : orderC c) (x : O) => x • ρ a)
    (fun a b x => by simp [map_add, smul_add])
    (fun n a x => by rw [map_zsmul, smul_comm])
    (fun a x y => by simp [add_smul])
    (fun n a x => smul_assoc n x (ρ a)))

theorem tensAct_tmul (ρ : orderC c →+* Module.End O H) (a : orderC c) (x : O) :
    tensAct ρ (a ⊗ₜ x) = x • ρ a := by
  rfl

theorem tensAct_eig (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (v : K ⊗[O] H)
    (hv : v ∈ eigK ρ σ) (t : orderC c ⊗[ℤ] O) :
    ((tensAct ρ t).baseChange K) v = coordAt O c σ t • v := by
  have hv' : ∀ a : orderC c, (ρ a).baseChange K v = σ a • v := fun a =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tensAct_tmul, LinearMap.baseChange_smul, LinearMap.smul_apply, hv' a]
    show x • ((σ a : K) • v) = (σ a * algebraMap O K x) • v
    rw [mul_smul, algebraMap_smul, smul_comm]
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_apply, h₁, h₂, map_add, add_smul]

theorem inK_apply_map (f : Module.End O H) (h : H) :
    inK (O := O) K H (f h) = (f.baseChange K) (inK K H h) := by
  simp [inK, LinearMap.baseChange_tmul]

theorem iSupIndep_and_smul_mem_iSup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ hcard D _ hclr I _ φ _ H _ _ ρ Fil B hlat hint
  have hfree : Module.Free O H := hlat.1
  have hinj : Function.Injective (inK (O := O) K H) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
      (IsFractionRing.injective O K)
    have : inK (O := O) K H = (LinearMap.rTensor H (Algebra.linearMap O K)) ∘ₗ
        (TensorProduct.lid O H).symm.toLinearMap := by
      ext h; simp [inK]
    rw [this]; exact h1.comp (TensorProduct.lid O H).symm.injective
  have hindK := hint.submodule_iSupIndep
  have htop : ∀ v : K ⊗[O] H, v ∈ ⨆ σ, eigK ρ σ := fun v => by
    rw [hint.submodule_iSup_eq_top]; trivial
  constructor
  · intro σ
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hle : (⨆ j, ⨆ (_ : j ≠ σ), eigLat ρ j) ≤
        ((⨆ j, ⨆ (_ : j ≠ σ), eigK ρ j).restrictScalars O).comap (inK K H) := by
      refine iSup₂_le fun j hj y hy => ?_
      exact (le_iSup₂ (f := fun j (_ : j ≠ σ) => eigK ρ j) j hj) hy
    have h0 := (Submodule.disjoint_def.1 (hindK σ)) _ hx1 (hle hx2)
    exact hinj (by rw [h0, map_zero])
  · have hfin : Finite (E →+* K) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    letI := Fintype.ofFinite (E →+* K)
    choose t ht using hclr
    have hA : ∀ (σ σ' : E →+* K) v, v ∈ eigK ρ σ' →
        ((tensAct ρ (t σ)).baseChange K) v = if σ' = σ then algebraMap O K D • v else 0 := by
      intro σ σ' v hv
      rw [tensAct_eig ρ σ' v hv, ht σ σ']
      split_ifs <;> simp
    have hsum : ∀ v : K ⊗[O] H, ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v := by
      intro v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [Finset.sum_congr rfl (fun σ _ => hA σ σ' w hw)]
        simp
      · simp
      · intro x y hx hy
        simp only [map_add, Finset.sum_add_distrib, smul_add] at hx hy ⊢
        rw [hx, hy]
    have hmem : ∀ σ v, ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ := by
      intro σ v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [hA σ σ' w hw]
        split_ifs with h
        · subst h; exact Submodule.smul_mem _ _ hw
        · exact zero_mem _
      · simp
      · intro x y hx hy
        simp only [map_add] at hx hy ⊢
        exact add_mem hx hy
    intro h
    have key : ∑ σ, tensAct ρ (t σ) h = D • h := by
      apply hinj
      rw [map_sum, map_smul]
      simp_rw [inK_apply_map, hsum, algebraMap_smul]
    rw [← key]
    refine Submodule.sum_mem _ fun σ _ => (le_iSup (fun σ => eigLat ρ σ) σ) ?_
    show inK K H _ ∈ eigK ρ σ
    rw [inK_apply_map]
    exact hmem σ _

end GlobalTheory.EigenLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegrality
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.ScaledRestr

theorem inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) := inferInstance
  unfold inK
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors O)]
  intro c
  intro x y hxy
  exact smul_right_injective H (nonZeroDivisors.coe_ne_zero c) hxy

theorem exists_scaled_image {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {H : Type} [AddCommGroup H] [Module O H] {I : Type}
    (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (D : O) (e f : I → H)
    (hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) (hG : IsGens φ ρ e f)
    (N : Module.End K (K ⊗[O] H)) (i : I) (hN : IsLower ρ (φ i) (e i) (f i) N) (h : H) :
    ∃ m : H, inK K H m = algebraMap O K D • N (inK K H h) := by
  have key : ∀ x ∈ ⨆ σ : E →+* K, eigLat ρ σ, ∃ m : H, inK K H m = N (inK K H x) := by
    intro x hx
    refine Submodule.iSup_induction (fun σ : E →+* K => eigLat ρ σ)
      (motive := fun x => ∃ m : H, inK K H m = N (inK K H x)) hx ?_ ?_ ?_
    · intro σ x hx
      by_cases hσ : σ = φ i
      · subst hσ
        rw [(hG i).1, Submodule.mem_span_singleton] at hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨u • f i, ?_⟩
        rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul_of_tower, hN.1]
      · refine ⟨0, ?_⟩
        have hx' : inK K H x ∈ eigK ρ σ := hx
        rw [hN.2 σ hσ _ hx', LinearMap.map_zero]
    · exact ⟨0, by simp⟩
    · intro x y hx hy
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]⟩
  obtain ⟨m, hm⟩ := key _ (hD h)
  refine ⟨m, ?_⟩
  rw [hm, LinearMap.map_smul, LinearMap.map_smul_of_tower, algebraMap_smul]

end GlobalTheory.ScaledRestr

namespace GlobalTheory.ScaledRestr

theorem scaledRestr_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hlat hEig e f hG N hN i
  haveI : Module.Free O H := hlat.1
  have hinj := inK_injective (O := O) K H
  have hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := hEig.2.2.1.2
  let g : H →ₗ[O] K ⊗[O] H := (algebraMap O K D) • ((N i).restrictScalars O ∘ₗ inK K H)
  have hg : ∀ h, g h ∈ LinearMap.range (inK K H) := by
    intro h
    obtain ⟨m, hm⟩ := exists_scaled_image φ ρ D e f hD hG (N i) i (hN i) h
    exact ⟨m, hm⟩
  refine ⟨(LinearEquiv.ofInjective (inK K H) hinj).symm.toLinearMap ∘ₗ (g.codRestrict _ hg), ?_, ?_⟩
  · intro h
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this
  · intro M hM
    ext h
    apply hinj
    rw [hM h]
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this.symm

end GlobalTheory.ScaledRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlipStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_graded_comm_of_isFlip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  first | exact @GlobalTheory.EtC.Pair.cup_flip | exact GlobalTheory.EtC.Pair.cup_flip | (intros; apply GlobalTheory.EtC.Pair.cup_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSectionStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  first | exact @GlobalTheory.PullBdd.pull_isBddSec | exact GlobalTheory.PullBdd.pull_isBddSec | (intros; apply GlobalTheory.PullBdd.pull_isBddSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
section
noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

namespace GlobalTheory.DeformedSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def dTerm (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (k + m i))

theorem dTerm_zero (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]

theorem dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

example (φ : E →+* ℂ) (x : E) :
    dTerm (fun _ : Unit => φ) 4 (fun _ => 1) 0 x = -4 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 5 := by
  simp [dTerm, defCoord]

end GlobalTheory.DeformedSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ), ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+ CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n) (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) → (∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ev β.1 0 n (by simp) U x = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = ev γ.1 k s hs V (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) → e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.EtC.DiscCoch.model) | (exact GlobalTheory.EtC.DiscCoch.model) | (intros; apply GlobalTheory.EtC.DiscCoch.model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  first | (exact @GlobalTheory.EtC.eqv_basic) | (exact GlobalTheory.EtC.eqv_basic) | (intros; apply GlobalTheory.EtC.eqv_basic  <;> assumption)
end

