import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
import GroundTheory.AutomorphicForms.HarishChandraCentre.Fischer

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.Consequences
section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def casimirGL2 : U 2 :=
  (1 / 2 : ℂ) • ((e (0, 0) - e (1, 1)) * (e (0, 0) - e (1, 1))) + e (0, 1) * e (1, 0) +
    e (1, 0) * e (0, 1)

theorem rep_center_apply_of_highestWeight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    (z : Subalgebra.center ℂ (U n)) :
    φ z v = eval (lam + rhoVec n) (harishChandraHom z) • v := by
  rw [rep_apply_of_highestWeight φ lam hup hH
    (commute_e_diag_of_mem (mem_centralizerT_of_mem_center z.2)), eval_harishChandraHom,
    add_sub_cancel_right]

def conjAlgHom (g : (gl n)ˣ) : gl n →ₐ[ℂ] gl n where
  toFun X := (g : gl n) * X * ↑g⁻¹
  map_one' := by simp
  map_mul' X Y := by
    simp only [mul_assoc]; rw [← mul_assoc (↑g⁻¹ : gl n) (g : gl n), Units.inv_mul, one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      Units.mul_inv]

noncomputable def conjU (g : (gl n)ˣ) : U n →ₐ[ℂ] U n :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (conjAlgHom g).toLieHom)

theorem conjU_ι (g : (gl n)ˣ) (X : gl n) :
    conjU g (UniversalEnvelopingAlgebra.ι ℂ X) = UniversalEnvelopingAlgebra.ι ℂ ((g : gl n) * X * ↑g⁻¹) := by
  simp [conjU, conjAlgHom]

theorem conjU_conjU_inv (g : (gl n)ˣ) (u : U n) : conjU g (conjU g⁻¹ u) = u := by
  have : (conjU g).comp (conjU g⁻¹) = AlgHom.id ℂ (U n) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext X
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.toLieHom_apply, AlgHom.comp_apply,
      conjU_ι, AlgHom.id_apply, inv_inv]
    congr 1
    simp [mul_assoc]
  exact congrArg (fun F : U n →ₐ[ℂ] U n => F u) this

theorem conjU_mem_center {g : (gl n)ˣ} {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    conjU g z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro u
  rw [← conjU_conjU_inv g u, ← map_mul, ← map_mul, hz]

theorem rep_center_apply_mem_span_of_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) (g : (gl n)ˣ) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (conjU g (e a)) v = 0)
    (hH : ∀ k, φ (conjU g (e (k, k))) v = lam k • v) {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    ∃ c : ℂ, φ z v = c • v := by
  have hz' : conjU g⁻¹ z ∈ Subalgebra.center ℂ (U n) := conjU_mem_center hz
  refine ⟨eval (lam + rhoVec n) (harishChandraHom ⟨_, hz'⟩), ?_⟩
  have := rep_center_apply_of_highestWeight (φ.comp (conjU g)) lam hup hH ⟨_, hz'⟩
  simpa [conjU_conjU_inv] using this

end GroundTheory.Automorphic.HarishChandra
end

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre.Injective
section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem exists_adjoint (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by
  induction u using U.induction with
  | halg r =>
    refine ⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]
  | hι X =>
    refine ⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩
    rw [ι_eq_sum_e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left,
      fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]
  | hmul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun f g => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]
  | hadd a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun f g => ?_⟩
    rw [map_add, LinearMap.add_apply, fischer_add_left, ha', hb', map_add, LinearMap.add_apply,
      fischer_add_right]

theorem eq_zero_of_mem_center_of_hcProjLin_eq_zero {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by
  obtain ⟨z', hz'⟩ := exists_adjoint z
  have hc : ∀ u : U n, u * z = z * u := fun u => (Subalgebra.mem_center_iff.1 hz) u
  apply eq_zero_of_rho_zero_eq_zero
  refine eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_
  · intro i j
    rw [← rho_zero_e, ← map_mul, ← map_mul, hc]
  · rw [← map_mul, ← map_mul, hc]
  · intro v μ hup hwt
    have := rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v)
      (fun a ha => by
        rw [show e a = e (a.1, a.2) from rfl, rho_zero_e]
        exact hup a.1 a.2 ha)
      (fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)
      (fun k => hc (e (k, k)))
    rw [this, h, map_zero, zero_smul]

theorem hcProjLin_injOn_center :
    Set.InjOn (hcProjLin (n := n)) (Subalgebra.center ℂ (U n) : Set (U n)) := by
  intro z hz z' hz' h
  have := eq_zero_of_mem_center_of_hcProjLin_eq_zero (Subalgebra.sub_mem _ hz hz')
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.1 this

theorem translate_neg_translate (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_translate, eval_translate, neg_add_cancel_right]

theorem translate_injective (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) :=
  Function.LeftInverse.injective (translate_neg_translate c)

theorem harishChandraHom_injective : Function.Injective (harishChandraHom (n := n)) := by
  intro z z' h
  rw [harishChandraHom_apply, harishChandraHom_apply] at h
  exact Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))

end GroundTheory.Automorphic.HarishChandra
end

