import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3507

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoMod
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

open scoped TensorProduct

private theorem finite_projective_of_free_int (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N] :
    Module.Finite (𝓞 E) N ∧ Module.Projective (𝓞 E) N := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) N
  haveI : Module.IsTorsionFree (𝓞 E) N := by
    refine Module.isTorsionFree_iff_smul_eq_zero.2 fun a x hax => ?_
    by_contra hk
    push_neg at hk
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    have h0 : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hk.1
    have h1 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul, hax, smul_zero]
    exact hk.2 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast h0))
  haveI : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

private theorem finrank_quot_tensor {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    [Module.Finite O N] [Module.Projective O N] (I : Ideal O) [I.IsMaximal] :
    Module.finrank (O ⧸ I) ((O ⧸ I) ⊗[O] N) = Module.finrank O N := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := O) (M := N) (S := O ⧸ I) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

private theorem one_tmul_eq_zero_iff {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (x : N) :
    (1 : O ⧸ I) ⊗ₜ[O] x = 0 ↔ x ∈ I • (⊤ : Submodule O N) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul N I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

private theorem one_tmul_surjective {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O)
    (t : (O ⧸ I) ⊗[O] N) : ∃ x : N, (1 : O ⧸ I) ⊗ₜ[O] x = t := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.quotTensorEquivQuotSMul N I t)
  refine ⟨x, (TensorProduct.quotTensorEquivQuotSMul N I).injective ?_⟩
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, hx]

theorem exists_ker_vec_of_not_onto_mod {O P X : Type} [CommRing O] [IsDomain O] [AddCommGroup P] [Module O P]
    [Module.Finite O P] [Module.Projective O P] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (f : P →ₗ[O] X) (hr : Module.finrank O P = Module.finrank O X) (I : Ideal O)
    (hI : I.IsMaximal) (hi : LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≠ ⊤) :
    ∃ v : P, f v ∈ I • (⊤ : Submodule O X) ∧ ∃ ℓ : P →ₗ[O] O, ℓ v ∉ I := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have hns : ¬ Function.Surjective (f.baseChange (O ⧸ I)) := fun hs => hi <| eq_top_iff.2 fun x _ => by
    obtain ⟨t, ht⟩ := hs (1 ⊗ₜ x)
    obtain ⟨v, rfl⟩ := one_tmul_surjective I t
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub, one_tmul_eq_zero_iff] at ht
    have : x = f v - (f v - x) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left ⟨v, rfl⟩) (Submodule.mem_sup_right ht)
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_quot_tensor, finrank_quot_tensor, hr]), injective_iff_map_eq_zero] at hns
  push_neg at hns
  obtain ⟨t, ht, ht0⟩ := hns
  obtain ⟨v, rfl⟩ := one_tmul_surjective I t
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at ht
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ I) ht0
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property I.mkQ
    ((g.restrictScalars O).comp (TensorProduct.mk O (O ⧸ I) P 1)) I.mkQ_surjective
  refine ⟨v, ht, ℓ, fun hv => hg ?_⟩
  have := LinearMap.congr_fun hℓ v
  exact this.symm.trans ((Submodule.Quotient.mk_eq_zero I).2 hv)

theorem IsOpp.exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  intro E _ _ _ H D X _ _ _ _ y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E X
  have hrank : Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) X := by
    have := h.finrank_int_eq
    rw [GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z'] at this
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos this).trans hr
  refine exists_ker_vec_of_not_onto_mod (y.comp Z'.subtype) hrank 𝔭 h𝔭 ?_
  rwa [LinearMap.range_comp, Submodule.range_subtype]

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullbackWeightZero

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)), IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y V f S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero

theorem h1cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := GlobalTheory.T.invariant_fields_cech_h1_relation

theorem liepush : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := GlobalTheory.T.exists_logDeriv_polarization_raynaud_eq_pullback

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (c' : Fin g → R) (N : Fin g → Fin n → R)
    (M : Fin n → Fin g → R) (hNM : ∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) (X : Fin g → Γ₀) :
    ∑ a, κ (c' a) * X a = ∑ b, κ (∑ a, c' a * N a b) * ∑ a', κ (M b a') * X a' := by
  have e : ∀ a', ∑ b, (∑ a, c' a * N a b) * M b a' = c' a' := by
    intro a'
    simp_rw [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hNM]
    simp
  simp_rw [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, e]

theorem h1_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin n → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', pbT Y.q.left (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') + (pbT Y.q.left (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - pbT Y.q.left (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz
  obtain ⟨g, w, dd', M, N, hw, hsp, hNM, hdl⟩ := liepush R Dd O oa Y n v dd hdd
  obtain ⟨c', y, hc'⟩ := h1cover R Dd g w dd' hw hsp J V j hcov hle z hz
  refine ⟨fun b => ∑ a, c' a * N a b, y, fun i i' => ?_⟩
  have hW : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
      Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
    Y.q.left.preimage_mono (inf_le_inf (hle i) (hle i'))
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  rw [hc' i i', GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_right le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_left le_rfl]
  congr 1
  simp only [hdl _ _ _ _ hW, GlobalTheory.KS.pbT_sum, GlobalTheory.KS.pbT_mul]
  simp only [GlobalTheory.KS.pbT_constFn _ _ hW, GlobalTheory.KS.pbT_constFn _ Y.q.left (O₀ := V i ⊓ V i') (O := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (inf_le_inf (hle i) (hle i')) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) c' N M hNM _

theorem exists_comb_dlg_add_cob : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz hw
  have hA := descend R Dd.toPre O oa Y
  have hB := isWt_pbT R Dd.toPre O oa Y
  choose z' hz' using fun i i' => (hA (V i ⊓ V i') (z i i') (hw i i')).exists
  have hcoc : IsCoc V z' := by
    intro i i' i''
    apply (hA (V i ⊓ V i' ⊓ V i'') _ (hB _ (rsT (z' i i'') (V i ⊓ V i' ⊓ V i'')))).unique _ rfl
    rw [GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl, GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) le_rfl,
      GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) le_rfl]
    have e1 : rsT (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i']; exact GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left _
    have e2 : rsT (z i' i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i' i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i' i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_right) inf_le_right) _
    have e3 : rsT (z i i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_left) inf_le_right) _
    rw [← e1, ← e2, ← e3]
    exact hz i i' i''
  obtain ⟨c, y', hc⟩ := h1_pull R Dd O oa Y n v dd hdd J V j hcov hle z' hcoc
  refine ⟨c, fun i => pbT Y.q.left (y' i) (Y.q.left ⁻¹ᵁ V i), fun i => hB _ _, fun i i' => ?_⟩
  rw [GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left, GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_right, ← hc i i']
  exact (hz' i i').symm

end GlobalTheory.PullbackWeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreIndep
open MonObj

set_option maxHeartbeats 2000000 in

theorem fibre_indep' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ιA : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ιA → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ιA ⁻¹ᵁ W i)), (∀ i i', (ιA.appLE (W i ⊓ W i') (ιA ⁻¹ᵁ W i ⊓ ιA ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  intro E _ _ _ H X t _hprop _hamp hK U n v hv hb δ hδ hδ0 hδt J W j hWa hWcov hWU hj m hm A _ ιA hι r h' hcob
  haveI := hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  set q := Ideal.Quotient.mk m with hq
  set x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap q ≫ chart U with hx0
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have hT : ∀ b, IsTanAtG t x0 (spMap (dualMap q) ≫ v b) := fun b => GlobalTheory.VertSpanZero.isTanAtG_bc t q (hv b)
  let uR : Fin n → (tEpsG (chart U) ⟶ t.G) := fun b => Over.homMk (spMap (epsMul (r b)) ≫ v b) (by
    change (spMap (epsMul (r b)) ≫ v b) ≫ t.G.hom = spMap (algebraMap _ (DualNumber _)) ≫ chart U
    rw [Category.assoc, (hv b).1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      GlobalTheory.VertSpanZero.epsMul_comp_algebraMap])
  obtain ⟨xR, hxRdef⟩ : ∃ xR : tEpsG (chart U) ⟶ t.G, xR = (List.ofFn uR).prod := ⟨_, rfl⟩
  have hxR : IsCombAtG t (chart U) v r xR.left := ⟨uR, fun b => rfl, by rw [hxRdef]⟩
  have eq0 : (dualMap q).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap (Γ(X, U.1) ⧸ m) (DualNumber (Γ(X, U.1) ⧸ m))).comp q := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let jq : tEpsG x0 ⟶ tEpsG (chart U) := Over.homMk (spMap (dualMap q)) (by
    change spMap (dualMap q) ≫ spMap (algebraMap _ (DualNumber _)) ≫ chart U = spMap (algebraMap _ (DualNumber _)) ≫ spMap q ≫ chart U
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, eq0])
  obtain ⟨P, hPdef⟩ : ∃ P : tEpsG x0 ⟶ t.G, P = jq ≫ xR := ⟨_, rfl⟩
  have hPl : P.left = spMap (dualMap q) ≫ xR.left := by rw [hPdef]; rfl
  have hP : IsCombAtG t x0 (fun b => spMap (dualMap q) ≫ v b) (fun b => q (r b)) P.left := by
    refine ⟨fun b => jq ≫ uR b, fun b => ?_, ?_⟩
    · change spMap (dualMap q) ≫ spMap (epsMul (r b)) ≫ v b = spMap (epsMul (q (r b))) ≫ spMap (dualMap q) ≫ v b
      have e1 : (dualMap q).comp (epsMul (r b)) = (epsMul (q (r b))).comp (dualMap q) := by
        apply RingHom.ext; intro z; ext
        · simp [epsMul, dualMap]
        · simp [epsMul, dualMap, mul_comm]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ v b) e1
    · rw [← GlobalTheory.FirstOrderValue.comp_prod_ofFn, ← hxRdef, hPdef]
  have hPt : spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left := by
    obtain ⟨u', hu', hu'P⟩ := hP
    let s : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom) (by
      change _ ≫ spMap (algebraMap _ _) ≫ x0 = x0
      rw [← Category.assoc, GlobalTheory.VertSpanZero.spMap_fst_algebraMap, Category.id_comp])
    have hs : ∀ b, s ≫ u' b = 1 := fun b => Over.OverMorphism.ext (by
      change spMap _ ≫ (u' b).left = _
      rw [hu' b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.VertSpanZero.fst_comp_epsMul]
      exact (hT b).2)
    have h1 : s ≫ (List.ofFn u').prod = 1 := by
      rw [GlobalTheory.FirstOrderValue.comp_prod_ofFn]; simp [hs]
    have h2 : (s ≫ (List.ofFn u').prod).left = (1 : Over.mk x0 ⟶ t.G).left := by rw [h1]
    rw [Over.comp_left, hu'P] at h2
    exact h2

  have hgen : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L P), c.IsGen := by
    let T := tEpsG x0
    let π : (T ⊗ t.G).left ⟶ Sp (DualNumber (Γ(X, U.1) ⧸ m)) := (fst T t.G).left
    let τ : (T ⊗ t.G).left ⟶ t.G.left := (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G]).left
    let ρ : (T ⊗ t.G).left ⟶ t.G.left := (snd T t.G).left
    have wπ : π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) ≫ x0 = (T ⊗ t.G).hom := Over.w (fst T t.G)
    have wρ : ρ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (snd T t.G)
    have wτ : τ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G])
    obtain ⟨ρ', hρ', hρs⟩ : ∃ ρ' : (T ⊗ t.G).left ⟶ A.left, ρ' ≫ ιA = ρ ∧
        ρ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift ρ _ wρ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    obtain ⟨τ', hτ', hτs⟩ : ∃ τ' : (T ⊗ t.G).left ⟶ A.left, τ' ≫ ιA = τ ∧
        τ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift τ _ wτ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    have hpts : ∀ y, τ'.base y = ρ'.base y := by
      intro y
      obtain ⟨K, _, z, ⟨p, rfl⟩, hz⟩ := GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points E H X t _ x0 P hPt y
      have hzz : z ≫ τ' = z ≫ ρ' := hι.1.hom_ext (by rw [Category.assoc, Category.assoc, hτ', hρ']; exact hz)
        (by rw [Category.assoc, Category.assoc, hτs, hρs])
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzz]
    have hιU : ∀ z, ιA.base z ∈ t.G.hom ⁻¹ᵁ U.1 := fun z => by
      show (ιA ≫ t.G.hom).base z ∈ U.1
      rw [hι.1.w, hx0, ← Category.assoc, Scheme.Hom.comp_apply]
      have h : (chart U).base ((A.hom ≫ spMap q).base z) ∈ Set.range (chart U).base := ⟨_, rfl⟩
      rwa [chart, U.2.range_fromSpec] at h
    have e : (fun n : Fin 2 => ![τ', ρ'] n ≫ ιA) = ![τ, ρ] := by
      funext n; fin_cases n
      · exact hτ'
      · exact hρ'
    have key := GlobalTheory.KS.DlogPol.exists_gen (K := Γ(X, U.1) ⧸ m) π τ' ρ' (fun y W hy => by rwa [← hpts y]) ιA t.PP.L
      t.PP.isLB (fun a b => GlobalTheory.KS.pbT ιA (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b)) ?_ (GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts E H X t U n δ hδ J W j hWa hWcov hWU hj m A ιA hι r h' hcob)
    · rw [e] at key
      exact key
    intro a b y ha hb
    beta_reduce
    have hτy : τ.base y = ρ.base y := by
      rw [← hτ', ← hρ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpts]
    have hρU : ρ.base y ∈ t.G.hom ⁻¹ᵁ U.1 := by rw [← hρ', Scheme.Hom.comp_apply]; exact hιU _
    have ha' : ρ.base y ∈ t.PP.L.U a := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact ha
    have hb' : ρ.base y ∈ t.PP.L.U b := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact hb
    have hyO : ρ.base y ∈ (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) := ⟨⟨ha', hρU⟩, ⟨hb', hρU⟩⟩
    have hOab : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.PP.L.U a ⊓ t.PP.L.U b :=
      inf_le_inf inf_le_left inf_le_left
    have hOU : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.G.hom ⁻¹ᵁ U.1 :=
      inf_le_left.trans inf_le_right
    have hρ'y : ρ'.base y ∈ ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b := by
      rw [← hpts y]; exact ⟨ha, hb⟩
    have e2a := GlobalTheory.T.firstOrder_translation_formula_germs E H X t U n v hv δ hδ hδ0 hδt r xR hxR (Γ(X, U.1) ⧸ m) q P hPl
    have e2 := e2a _ hOU (resG t.G.left hOab (t.PP.L.g a b).val) y hyO
    rw [GlobalTheory.KS.DlogPol.gs_pbT ρ' ιA y (O₀ := (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (O := ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b) (fun z hz => ⟨⟨hz.1, hιU z⟩, ⟨hz.2, hιU z⟩⟩) hρ'y, hτ', hρ',
      ← gs_res τ y hOab (hτy ▸ hyO), ← gs_res ρ y hOab hyO]
    rw [e2]
    have hκ : (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * (δ c _ (resG t.G.left hOab (t.PP.L.g a b).val) *
        resG t.G.left hOab (t.PP.L.g a b)⁻¹.val)) = (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) *
        δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)) * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    have hFF : resG t.G.left hOab (t.PP.L.g a b).val * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hFF' := congrArg (gs ρ y _) hFF
    rw [gs_mul ρ y _ hyO, GlobalTheory.KS.DlogPol.gs_one ρ y _ hyO] at hFF'
    rw [hκ, gs_mul ρ y _ hyO]
    linear_combination (-(gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Γ(X, U.1) ⧸ m)))).inv.hom DualNumber.eps) *
      gs ρ y _ (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)))) * hFF'
  have hP1 : P = toUnit _ ≫ η[t.G] := hK (DualNumber (Γ(X, U.1) ⧸ m)) _ P fun p => by
    obtain ⟨c, hc⟩ := hgen
    exact ⟨⊤, trivial, gen_chartPull (GlobalTheory.chartPullPull (Out.translDiff t.G t.PP.L P) _) c hc⟩
  have hP1' : P.left = (1 : tEpsG x0 ⟶ t.G).left := by rw [hP1, Hom.one_def]
  have h0 := GlobalTheory.VertSpanZero.isCombAtG_zero t x0 _ hT
  have huniq := (hB.2 (Γ(X, U.1) ⧸ m) q _ (GlobalTheory.VertSpanZero.isTanAtG_one t x0)).unique (hP1' ▸ hP) h0
  intro b
  have := congrFun huniq b
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end GlobalTheory.FibreIndep

theorem GlobalTheory.FibreIndep.fibre_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := GlobalTheory.FibreIndep.fibre_indep'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  first | (exact @GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (exact GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (intros; apply GlobalTheory.KerKilledFibre.fibreKilled_of_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndex
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

theorem finrank_balBil_le_of_smul_mem_range {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar X) ≤ Module.finrank ℤ (balBil bar Y) := by
  let f' : Y →ₗ[ℤ] X := f.toAddMonoidHom.toIntLinearMap
  have hf' : ∀ y, f' y = f y := fun y => rfl
  let Φ : balBil bar X →ₗ[ℤ] balBil bar Y :=
    { toFun := fun β => ⟨(β : LinearMap.BilinForm ℤ X).compl₁₂ f' f', by
        intro a y z
        have := β.2 a (f y) (f z)
        simpa [hf', LinearMap.compl₁₂_apply, map_smul] using this⟩
      map_add' := fun β β' => by ext; simp
      map_smul' := fun n β => by ext; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext x x'
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨y', hy'⟩ := hf x'
    have h0 : (β : LinearMap.BilinForm ℤ X) (f y) (f y') = 0 := by
      have := congrArg (fun γ : balBil bar Y => (γ : LinearMap.BilinForm ℤ Y) y y') hβ
      simpa [Φ, hf'] using this
    rw [hy, hy'] at h0
    have h1 : ((m : ℤ) * m) * (β : LinearMap.BilinForm ℤ X) x x' = 0 := by
      rw [← h0]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    have hm' : ((m : ℤ) * m) ≠ 0 := by positivity
    simpa using (mul_eq_zero.mp h1).resolve_left hm'
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_balBil_eq_of_finiteIndex {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : Function.Injective f)
    (hr : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar Y) = Module.finrank ℤ (balBil bar X) := by
  let e := LinearEquiv.ofInjective f hf
  let c : X →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (m • LinearMap.id) (fun x => by simpa using hr x)
  let g : X →ₗ[O] Y := e.symm.toLinearMap ∘ₗ c
  have hfg : ∀ x, f (g x) = m • x := by
    intro x
    have h1 : e (g x) = c x := by simp [g]
    have h2 := congrArg Subtype.val h1
    simpa [e, c] using h2
  have hgf : ∀ y, g (f y) = m • y := by
    intro y; apply hf; rw [hfg, map_nsmul]
  apply le_antisymm
  · exact finrank_balBil_le_of_smul_mem_range bar Y X g m hm (fun y => ⟨f y, hgf y⟩)
  · exact finrank_balBil_le_of_smul_mem_range bar X Y f m hm hr

end GlobalTheory.BalRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsPi
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J]

def formOfFamily (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : LinearMap.BilinForm ℤ (J → 𝓞 E) :=
  LinearMap.mk₂ ℤ (fun y z => ∑ i, ∑ j, φ i j (H.bar (y i) * z j))
    (by intro y y' z; simp [map_add, add_mul, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, smul_mul_assoc, Finset.smul_sum])
    (by intro y z z'; simp [map_add, mul_add, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, mul_smul_comm, Finset.smul_sum])

theorem formOfFamily_apply (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) (y z : J → 𝓞 E) :
    formOfFamily H J φ y z = ∑ i, ∑ j, φ i j (H.bar (y i) * z j) := rfl

theorem formOfFamily_mem (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : formOfFamily H J φ ∈ balBil H.bar (J → 𝓞 E) := by
  intro a y z
  simp only [formOfFamily_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf

def balBilEquiv : balBil H.bar (J → 𝓞 E) ≃ₗ[ℤ] (J → J → (𝓞 E →ₗ[ℤ] ℤ)) where
  toFun β := fun i j => (β.1 (Pi.single i 1)) ∘ₗ LinearMap.single ℤ (fun _ : J => 𝓞 E) j
  map_add' β β' := by ext; simp
  map_smul' c β := by ext; simp
  invFun φ := ⟨formOfFamily H J φ, formOfFamily_mem H J φ⟩
  left_inv β := by
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    have hy : y = ∑ i, y i • (Pi.single i (1 : 𝓞 E) : J → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      rcases eq_or_ne k i with rfl | h <;> simp [*]
    conv_rhs => rw [hy]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [β.2 (y i) (Pi.single i 1) z]
    conv_rhs => rw [← Finset.univ_sum_single (H.bar (y i) • z)]
    rw [map_sum]
    rfl
  right_inv φ := by
    funext i j
    refine LinearMap.ext fun c => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_apply, hj]
    · simp
    · intro i' _ hi; simp [Pi.single_apply, hi]
    · simp

theorem finrank_balBil_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J]
    [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) =
      Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  intro E _ _ _ H J _ _
  rw [(balBilEquiv H J).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap, Module.finrank_self, mul_one,
    NumberField.RingOfIntegers.rank, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

end GlobalTheory.BalRank
end
end

