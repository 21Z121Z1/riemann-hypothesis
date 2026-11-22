import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

section SlopeTestRemainingChoices

open GlobalTheory GlobalTheory.CM GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_lam_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) [IsCommMonObj P.A] {T : Over S}
    (z : T ⟶ P.A) (h : lam (cls P.L P.isLB) (fst T P.A ≫ z) (snd T P.A) = 0) : z = 1 := by
  have hL := P.isLB
  have hc : (cubeLB P.A ![fst T P.A ≫ z, snd T P.A] P.L).IsLB := LB.isLB_linComb hL _ _
  have g₂ : GlobalTheory.KerPow.HasGen P.L
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) :=
    (cls_eq_zero_iff hc).1 ((cls_cube_two hL _ _ hc).trans h)
  have g₃ : LocGen P.L (fst T P.A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T P.A).left z.left (b := (fst T P.A ≫ z).left) rfl
  have b₀ := locGen_base hL (fst T P.A).left (1 : T ⟶ P.A).left (b := (1 : T ⊗ P.A ⟶ P.A).left)
    (congrArg (fun q : T ⊗ P.A ⟶ P.A => q.left) (MonObj.comp_one (fst T P.A) : fst T P.A ≫ (1 : T ⟶ P.A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ P.A ⟶ P.A).left, (fst T P.A ≫ z).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen P.ktriv z (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T P.A ≫ z) * snd T P.A).left * (k (fst T P.A ≫ z).left)⁻¹ * (k (snd T P.A).left)⁻¹ *
    k (1 : T ⊗ P.A ⟶ P.A).left *
    (k (1 : T ⊗ P.A ⟶ P.A).left ^ (1 : ℤ) * k (fst T P.A ≫ z).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T P.A ≫ z) * snd T P.A).left ^ (1 : ℤ) * k (snd T P.A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end SlopeTestRemainingChoices

end GlobalTheory.KillSquare

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

theorem pow_sq_eq_one_of_lam_trivial : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  intro A _ hA M hM P ψ ρ N hψ hρ h1 h2 hiso T x hx
  haveI : IsCommMonObj A := hA.comm
  haveI := P.isAb
  have hL := P.isLB
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ P.A P.isAb P.L hL
  set ℓ := cls P.L hL
  set m := cls M hM

  have hlamA : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hpair : lam m (fst A A) (snd A A) = lam ℓ (fst A A ≫ ψ) (snd A A ≫ ψ) := by
    have hlamP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb hL _ _
    have e := (cls_eq_iff hlamA (pull_isLB hlamP _)).2 hiso
    exact (cls_cube_two hM (fst A A) (snd A A) hlamA).symm.trans (e.trans (Elliptic.cls_pull_lam hL _ _ _))

  have hx0 : lam m (fst A T) (snd A T ≫ x) = 0 := by
    rw [← Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamA _)]
    exact (cls_eq_zero_iff _).2 hx
  have e1 := congrArg (pull (lift (fst A T) (snd A T ≫ x)).left) hpair
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e1
  rw [e1] at hx0

  have e2 := congrArg (pull (lift (fst P.A T ≫ ρ) (snd P.A T)).left) hx0
  simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, Category.assoc] at e2
  have e3 : fst P.A T ≫ ρ ≫ ψ = fst P.A T ^ N := by
    rw [h2, MonObj.comp_pow, Category.comp_id]
  rw [e3, lam_pow_left hL hΘ, ← lam_pow_right hL hΘ, ← MonObj.comp_pow] at e2

  have hz : (x ≫ ψ) ^ N = 1 := by
    refine GlobalTheory.KillSquare.eq_one_of_lam_eq_zero P _ ?_
    have e4 := congrArg (pull (lift (snd T P.A) (fst T P.A)).left) e2
    simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at e4
    rw [lam_comm] at e4
    simpa only [Category.assoc] using e4
  rw [pow_mul]
  have e5 : x ^ N = (x ≫ ψ) ≫ ρ := by
    rw [Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  rw [e5, ← MonObj.pow_comp, hz, MonObj.one_comp]

end GlobalTheory.KillSquare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismDeterminantGenerator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetGen

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_gen_of_basis {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module B L'] {g : ℕ}
    (e : Module.Basis (Fin g) R L) (e' : Module.Basis (Fin g) B L') (φ : L →ₛₗ[algebraMap R B] L') (hφ : ∀ j, φ (e j) = e' j)
    (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧ ∀ v, δ' (fun j ↦ φ (v j)) = algebraMap R B (δ v) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hδ ▸ Submodule.mem_top : e.det ∈ Submodule.span R {δ})
  have h1 : c * δ e = 1 := by
    have := congrArg (fun f : L [⋀^Fin g]→ₗ[R] R ↦ f e) hc
    simpa [Module.Basis.det_self] using this
  refine ⟨algebraMap R B (δ e) • e'.det, eq_top_iff.2 fun ω _ ↦ Submodule.mem_span_singleton.2
    ⟨ω e' * algebraMap R B c, ?_⟩, fun v ↦ ?_⟩
  · rw [smul_smul, _root_.mul_assoc, ← map_mul, h1, map_one, _root_.mul_one, ← ω.eq_smul_basis_det e']
  · have hr : ∀ (x : L) (i : Fin g), e'.repr (φ x) i = algebraMap R B (e.repr x i) := fun x i ↦ by
      have : φ x = ∑ j, algebraMap R B (e.repr x j) • e' j := by
        conv_lhs => rw [← e.sum_repr x, map_sum]
        simp only [LinearMap.map_smulₛₗ, hφ]
      rw [this, e'.repr_sum_self]
    have hm : e'.toMatrix (fun j ↦ φ (v j)) = (algebraMap R B).mapMatrix (e.toMatrix v) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hr]
    conv_rhs => rw [δ.eq_smul_basis_det e]
    simp only [AlternatingMap.smul_apply, smul_eq_mul, map_mul, Module.Basis.det_apply, hm, RingHom.map_det]

theorem exists_gen_quot {H H' L L' : Type*} [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module B H'] [AddCommGroup L]
    [Module R L] [AddCommGroup L'] [Module B L'] {K I : Type*} [Fintype K] [Fintype I] {g : ℕ}
    (b : Module.Basis K R H) (b' : Module.Basis K B H') (bc : H →ₛₗ[algebraMap R B] H') (hb : ∀ k, bc (b k) = b' k)
    (t : I → B) (N : I → Module.End R H) (hN : ∀ i j, N i * N j = 0) (q : H →ₗ[R] L) (hq : Function.Surjective q)
    (q' : H' →ₗ[B] L') (hq' : Function.Surjective q')
    (hker : LinearMap.ker q' = Submodule.span B {d | ∃ x ∈ LinearMap.ker q, d = bc x + ∑ i, t i • bc (N i x)})
    (e : Module.Basis (Fin g) R L) (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧
      ∀ x : Fin g → H, δ' (fun j ↦ q' (bc (x j) + ∑ i, t i • bc (N i (x j)))) = algebraMap R B (δ fun j ↦ q (x j)) := by
  have hNN : ∀ i j x, N i (N j x) = 0 := fun i j x ↦ LinearMap.congr_fun (hN i j) x
  let nn : H →ₛₗ[algebraMap R B] H' :=
    { toFun x := bc x + ∑ i, t i • bc (N i x)
      map_add' x y := by
        simp only [map_add, smul_add, Finset.sum_add_distrib]; abel
      map_smul' r x := by
        simp only [map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum, smul_smul, mul_comm] }
  have nn_def : ∀ x, nn x = bc x + ∑ i, t i • bc (N i x) := fun _ ↦ rfl
  have nnN : ∀ i x, nn (N i x) = bc (N i x) := fun i x ↦ by simp [nn_def, hNN]
  have bc_eq : ∀ x, bc x = nn x - ∑ i, t i • nn (N i x) := fun x ↦ by simp only [nnN, nn_def x, add_sub_cancel_right]
  let φ : L →ₛₗ[algebraMap R B] L' :=
    ((LinearMap.ker q).liftQ (q' ∘ₛₗ nn) fun x hx ↦ by
      change nn x ∈ LinearMap.ker q'
      rw [hker]
      exact Submodule.subset_span ⟨x, hx, rfl⟩) ∘ₛₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hφ : ∀ x, φ (q x) = q' (nn x) := fun x ↦ by
    have : (q.quotKerEquivOfSurjective hq).symm (q x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have ext : ∀ l : H →ₗ[R] R, ∃ l' : H' →ₗ[B] B, ∀ x, l' (bc x) = algebraMap R B (l x) := fun l ↦
    ⟨b'.constr B fun k ↦ algebraMap R B (l (b k)), fun x ↦ by
      have h : ∀ k, (b'.constr B fun k ↦ algebraMap R B (l (b k))) (b' k) = algebraMap R B (l (b k)) :=
        fun k ↦ b'.constr_basis B _ k
      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum]
      conv_rhs => rw [← b.sum_repr x, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [bc.map_smulₛₗ, map_smul, hb, h, map_smul, smul_eq_mul, smul_eq_mul, map_mul]⟩
  have coord : ∀ l : L →ₗ[R] R, ∃ l' : L' →ₗ[B] B, ∀ v, l' (φ v) = algebraMap R B (l v) := fun l ↦ by
    obtain ⟨l₀, h₀⟩ := ext (l ∘ₗ q)
    choose l₁ h₁ using fun i ↦ ext (l ∘ₗ q ∘ₗ N i)
    let ξ : H' →ₗ[B] B := l₀ - ∑ i, t i • l₁ i
    have hξ : ∀ x, ξ (nn x) = algebraMap R B (l (q x)) := fun x ↦ by
      simp [ξ, nn_def, LinearMap.sum_apply, map_sum, h₀, h₁, hNN]
    have hk : LinearMap.ker q' ≤ LinearMap.ker ξ := by
      rw [hker, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      change ξ (nn x) = 0
      rw [hξ, LinearMap.mem_ker.1 hx, map_zero, map_zero]
    refine ⟨(LinearMap.ker q').liftQ ξ hk ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap, fun v ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hq v
    have : (q'.quotKerEquivOfSurjective hq').symm (q' (nn x)) = Submodule.Quotient.mk (nn x) :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply, hξ]
  have li : LinearIndependent B fun j ↦ φ (e j) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨l', hl'⟩ := coord (e.coord j)
    have := congrArg l' hc
    simpa [map_sum, hl', Finsupp.single_apply, apply_ite (algebraMap R B)] using this
  have sp : ⊤ ≤ Submodule.span B (Set.range fun j ↦ φ (e j)) := by
    have h1 : ∀ v, φ v ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun v ↦ by
      rw [← e.sum_repr v, map_sum]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h2 : ∀ x, q' (bc x) ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun x ↦ by
      rw [bc_eq, map_sub, map_sum, ← hφ]
      refine sub_mem (h1 _) (Submodule.sum_mem _ fun i _ ↦ ?_)
      rw [map_smul, ← hφ]
      exact Submodule.smul_mem _ _ (h1 _)
    intro w _
    obtain ⟨d, rfl⟩ := hq' w
    rw [← b'.sum_repr d, map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [map_smul, ← hb]
    exact Submodule.smul_mem _ _ (h2 _)
  obtain ⟨δ', h1, h2⟩ := exists_gen_of_basis e (Module.Basis.mk li sp) φ (fun j ↦ by simp) δ hδ
  refine ⟨δ', h1, fun x ↦ ?_⟩
  rw [← h2]
  simp only [hφ, nn_def]

end Alg

theorem nonempty_basis_lie (H : GlobalTheory.Published.AbelianDeRham.Hodge) {R : Type} [CommRing R] [IsLocalRing R] {A : Over (Sp R)} [GrpObj A]
    [IsCommMonObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {O : Type} [CommRing O]
    (a : OAct O A) : Nonempty (Module.Basis (Fin g) R (Serre.Lie a)) := by
  obtain ⟨hL, ⟨M, hM⟩, h1, h2, h3⟩ := H R A g hA hg
  haveI : Module.Free R (PrimitiveSubmodule A) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R (PrimitiveSubmodule A) = g := by
    have := h3 (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hs : Function.Surjective (PrimitiveSubmodule A).dualRestrict := fun l ↦
    ⟨l ∘ₗ (PrimitiveSubmodule A).projectionOnto M hM, LinearMap.ext fun c ↦ by simp⟩
  let E : (HdR A ⧸ Fil A) ≃ₗ[R] Module.Dual R (PrimitiveSubmodule A) :=
    (Submodule.quotEquivOfEq _ _ (Submodule.dualRestrict_ker_eq_dualAnnihilator _).symm).trans
      ((PrimitiveSubmodule A).dualRestrict.quotKerEquivOfSurjective hs)
  exact ⟨(Module.finBasisOfFinrankEq R _ hr).dualBasis.map (E.symm.trans (hL.quotEquiv a))⟩

theorem main : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC →
    ∀ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} →
      ∃ δ' : X'.DetGen, ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
        (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
        (∀ j, IsJetElt J X N m (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
          δ'.1 v' = algebraMap R J.B (δ.1 v) := by
  intro _ H _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X δ N hN m hm X' i pull hfil
  classical
  obtain ⟨e⟩ := nonempty_basis_lie H.2.1 X.ab X.dim X.rm
  obtain ⟨f1, f2, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  let p := Module.Free.chooseBasis R (primDR X.A)
  let p' := (Algebra.TensorProduct.basis J.B p).map (LinearEquiv.ofBijective _ hm)
  have hp : ∀ k, p' k = m.pull (p k) := fun k ↦ by
    simp only [p', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact (liftSemi_tmul m.pull 1 (p k)).trans (one_smul _ _)
  have hc : ∀ x c, hm.bcMap x (m.pull c) = algebraMap R J.B (x c) := fun x ↦ hm.corr_iff.2 rfl
  have hb : ∀ k, hm.bcMap (p.dualBasis k) = p'.dualBasis k := fun k ↦ p'.ext fun l ↦ by
    rw [Module.Basis.dualBasis_apply_self, hp, hc, Module.Basis.dualBasis_apply_self]
    split_ifs <;> simp
  have hj : ∀ x d, IsJetElt J X N m x d ↔ d = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := fun x d ↦ by
    constructor
    · intro h
      refine p'.ext fun l ↦ ?_
      rw [hp, h]
      simp [LinearMap.sum_apply, hc]
    · rintro rfl c
      simp [LinearMap.sum_apply, hc]
  have hπ : Function.Surjective J.π := fun r ↦ ⟨r • J.b ⟨0, by simp⟩, by simp [J.π_eq]⟩
  have hbij := GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective H.2.2.2.1 X'.ab X'.dim J.nil hπ rfl pull.grp
  have hL := (H.2.1 R X.A _ X.ab X.dim).1
  have hL' := (H.2.1 J.B X'.A _ X'.ab X'.dim).1
  obtain ⟨δ', h1, h2⟩ := exists_gen_quot p.dualBasis p'.dualBasis hm.bcMap hb J.t N hN.2.1 (hL.toLie X.rm)
    (hL.toLie_surjective _) (hL'.toLie X'.rm ∘ₗ crysToDR J.κ pull.grp) ((hL'.toLie_surjective _).comp hbij.2)
    (by
      rw [LinearMap.ker_comp, hL'.ker_toLie, hL.ker_toLie]
      simp only [← hj]
      exact hfil) e δ.1 δ.2
  refine ⟨⟨δ', h1⟩, fun x d v v' h ↦ ?_⟩
  obtain rfl : v = fun j ↦ hL.toLie X.rm (x j) := funext fun j ↦ ((hL.toLie_eq_iff _).2 (h j).2.1).symm
  rw [← h2]
  refine congrArg δ' (funext fun j ↦ ?_)
  rw [← (hj _ _).1 (h j).1]
  exact ((hL'.toLie_eq_iff _).2 (h j).2.2).symm

end GlobalTheory.JetGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct

section Aug

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

theorem JetRing.π_comp_algebraMap (J : JetRing R I n) : J.π.comp (algebraMap R J.B) = RingHom.id R := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one,
    ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
  simp

theorem JetRing.π_surjective (J : JetRing R I n) : Function.Surjective J.π := fun r =>
  ⟨algebraMap R J.B r, by simpa using RingHom.congr_fun J.π_comp_algebraMap r⟩

end Aug

theorem grpMor_isBC (P : AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))) :
    m.IsBC := by
  obtain ⟨-, -, PB, PR, -⟩ := P
  obtain ⟨C, _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback X.A (spMap (algebraMap R J.B))
  have eid : spMap J.π ≫ spMap (algebraMap R J.B) = 𝟙 _ := by
    rw [spMap_comp_spMap, J.π_comp_algebraMap]
    exact Spec.map_id _
  have w : 𝟙 X.A.left ≫ X.A.hom = (X.A.hom ≫ spMap J.π) ≫ spMap (algebraMap R J.B) := by
    rw [Category.assoc, eid, Category.comp_id, Category.id_comp]
  have e1 : hφ.1.lift _ _ w ≫ φ = 𝟙 _ := hφ.1.lift_fst _ _ _
  have e2 : hφ.1.lift _ _ w ≫ C.hom = X.A.hom ≫ spMap J.π := hφ.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl X.A).hom := inferInstanceAs (IsMonHom (𝟙 X.A))
  have hic : IsGrpPullback X.A C (spMap J.π) (hφ.1.lift _ _ w) :=
    hφ.cancel ((isGrpPullback_of_iso (Iso.refl X.A)).congr eid.symm e1.symm) e2
  have hC := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback X.ab hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 X.dim
  obtain ⟨bc, -⟩ := PB R X.A _ X.ab X.dim J.B C φ hφ
  have rg := PR _ C _ hC gC _ J.κ J.nil R J.π J.π_surjective rfl X.A _ hic
  have e : ∀ z, liftSemi m.pull z = (liftMor J.κ hic).pull (liftSemi (bcMor hφ).pull z) := fun z => by
    induction z with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r c =>
      rw [liftSemi_tmul, liftSemi_tmul, map_smul,
        ← GrpMor.pull_pull (bcMor hφ) (liftMor J.κ hic) m (fun _ => rfl) (by simpa using e1) c]
  have : ⇑(liftSemi m.pull) = (liftMor J.κ hic).pull ∘ liftSemi (bcMor hφ).pull := funext e
  unfold GrpMor.IsBC
  rw [this]
  exact rg.comp bc

end GlobalTheory.LatJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingComplexEmbedding
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet

variable {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n)

def coeffMap (x : J.B) : J'.B := J'.b.repr.symm (Finsupp.mapRange σ σ.map_zero (J.b.repr x))

variable {σ J J'}

theorem coeffMap_repr (x : J.B) (ν : Idx I n) : J'.b.repr (coeffMap σ J J' x) ν = σ (J.b.repr x ν) := by
  simp [coeffMap]

theorem coeffMap_add (x y : J.B) : coeffMap σ J J' (x + y) = coeffMap σ J J' x + coeffMap σ J J' y := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_zero : coeffMap σ J J' 0 = 0 := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_smul (r : R) (x : J.B) : coeffMap σ J J' (r • x) = σ r • coeffMap σ J J' x := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

theorem coeffMap_nsmul (k : ℕ) (x : J.B) : coeffMap σ J J' (k • x) = k • coeffMap σ J J' x := by
  rw [← Nat.cast_smul_eq_nsmul R k x, coeffMap_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem coeffMap_basis (ν : Idx I n) : coeffMap σ J J' (J.b ν) = J'.b ν := by
  refine J'.b.ext_elem fun ρ => ?_
  rw [coeffMap_repr, J.b.repr_self, J'.b.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem coeffMap_basis_mul (ν ν' : Idx I n) :
    coeffMap σ J J' (J.b ν * J.b ν') = J'.b ν * J'.b ν' := by
  rw [JetRing.mul J, JetRing.mul J']
  split_ifs
  · rw [coeffMap_nsmul, coeffMap_basis]
  · exact coeffMap_zero

theorem coeffMap_one : coeffMap σ J J' 1 = 1 := by
  rw [← J.one, coeffMap_basis, J'.one]

theorem coeffMap_mul (x y : J.B) : coeffMap σ J J' (x * y) = coeffMap σ J J' x * coeffMap σ J J' y := by
  have hx : x ∈ Submodule.span R (Set.range J.b) := J.b.mem_span x
  have hy : y ∈ Submodule.span R (Set.range J.b) := J.b.mem_span y
  induction hx using Submodule.span_induction generalizing y with
  | mem a ha =>
    obtain ⟨ν, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨ν', rfl⟩ := hc
      rw [coeffMap_basis_mul, coeffMap_basis, coeffMap_basis]
    | zero => rw [mul_zero, coeffMap_zero, mul_zero]
    | add u v _ _ hu hv => rw [mul_add, coeffMap_add, coeffMap_add, hu, hv, mul_add]
    | smul r u _ hu => rw [mul_smul_comm, coeffMap_smul, coeffMap_smul, hu, mul_smul_comm]
  | zero => rw [zero_mul, coeffMap_zero, zero_mul]
  | add u v _ _ hu hv => rw [add_mul, coeffMap_add, coeffMap_add, hu y hy, hv y hy, add_mul]
  | smul r u _ hu => rw [smul_mul_assoc, coeffMap_smul, coeffMap_smul, hu y hy, smul_mul_assoc]

variable (σ J J')

def coeffHom : J.B →+* J'.B where
  toFun := coeffMap σ J J'
  map_one' := coeffMap_one
  map_mul' := coeffMap_mul
  map_zero' := coeffMap_zero
  map_add' := coeffMap_add

theorem coeffHom_isDPMorphism : IsDPMorphism J.κ J'.κ (coeffHom σ J J') := by
  have hker : ∀ a ∈ RingHom.ker J.π, coeffHom σ J J' a ∈ RingHom.ker J'.π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [J'.π_eq, coeffHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeffMap_repr, ← J.π_eq, ha, map_zero]
  refine ⟨?_, fun {k} a ha => ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hker a ha
  · have hu : IsUnit ((k.factorial : ℕ) : J'.B) := by
      have : ((k.factorial : ℕ) : J'.B) = algebraMap ℂ J'.B (k.factorial : ℂ) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast k.factorial_ne_zero)).map _
    refine hu.mul_left_cancel ?_
    rw [J'.κ.factorial_mul_dpow_eq_pow (hker a ha), ← map_natCast (coeffHom σ J J'), ← map_mul,
      J.κ.factorial_mul_dpow_eq_pow ha, map_pow]

theorem exists_coeffHom : ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  ⟨coeffHom σ J J', fun x ν => coeffMap_repr x ν, coeffHom_isDPMorphism σ J J'⟩

theorem jet_coeffMap : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  by
  intro R _ σ I _ n J J'
  exact exists_coeffHom σ J J'

end GlobalTheory.LatJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelAction_isPullback_prodMap_torsor : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  first | exact @GlobalTheory.CharKer.pmap_isPullback_actMap | exact GlobalTheory.CharKer.pmap_isPullback_actMap | (intros; apply GlobalTheory.CharKer.pmap_isPullback_actMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinearStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_prod_bijective_semilinear : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.liftSemi_prod_bijective | exact GlobalTheory.liftSemi_prod_bijective | (intros; apply GlobalTheory.liftSemi_prod_bijective <;> assumption)
end

