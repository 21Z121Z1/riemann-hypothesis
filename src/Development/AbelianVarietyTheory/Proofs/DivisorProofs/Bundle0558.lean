import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwisted
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.LiftHc

theorem galAct_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (x : GL (Fin n) F) : galAct F F' n t (incl F F' n x) = incl F F' n x := by
  ext i j; simp [galAct_apply, gal, incl]

theorem inPar_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (x : GL (Fin n) F) :
    InPar a (incl F F' n x) ↔ InPar a x := by
  simp [InPar, incl, gal]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a n : ℕ) (x : GL (Fin n) F) (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi; simp [gal, hx i j hj hi]

theorem gal_id {F : Type} [Field F] (n : ℕ) (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem nrm_conj_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (y₀ : GL (Fin n) F) :
    nrm s ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) = (incl F F' n y₀)⁻¹ * nrm s δ * incl F F' n y₀ := by
  unfold nrm nrmG
  set c := incl F F' n y₀
  set L := List.range (Module.finrank F F')
  have h : ∀ i : ℕ, galAct F F' n (s ^ i) (c⁻¹ * δ * c) =
      MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ) := by
    intro i
    rw [map_mul, map_mul, map_inv, galAct_incl, MulAut.conj_apply, inv_inv]
  simp only [h]
  have e := map_list_prod (MulAut.conj c⁻¹) (L.map fun i => galAct F F' n (s ^ i) δ)
  rw [List.map_map] at e
  rw [show (fun i => MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ)) =
    (⇑(MulAut.conj c⁻¹) ∘ fun i => galAct F F' n (s ^ i) δ) from rfl, ← e, MulAut.conj_apply, inv_inv]

theorem count {G₀ G : Type} [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G)
    (H : Subgroup G) (T : G → ℂ) (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) :=
  GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres G₀ G ι H T hT

theorem blocks_twist {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (hn : n = a + b)
    (p x : GL (Fin n) F) (hp : InPar a p) (hx : InPar a x) :
    tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧
    brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) :=
  GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular F t a b n hn p x hp hx

theorem inPar_conj_adjoin {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ)
    (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hP : InPar a (y₀⁻¹ * γ * y₀)) : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) :=
  GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj F F' a n γ y₀ δ hA hP

theorem term (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) (y₀ : GL (Fin n) F) (p : GL (Fin n) F') (hp : InPar a p) :
    (if InPar a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)) then
      shLift s α (tlG a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p))) *
      shLift s β (brG a b ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)))
      else 0) =
    (if InPar a (y₀⁻¹ * γ * y₀) then α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0) := by
  have hle : a ≤ n := by omega
  obtain ⟨H, π, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  obtain ⟨H₀, π₀, hH₀, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  set c := incl F F' n y₀ with hc
  set δ₁ := c⁻¹ * δ * c with hδ₁def
  have hgc : gal (s : F' →+* F') n c = c := galAct_incl n s y₀
  have key : (c * p)⁻¹ * δ * gal (s : F' →+* F') n (c * p) = p⁻¹ * δ₁ * gal (s : F' →+* F') n p := by
    rw [map_mul, hgc, hδ₁def]; group
  by_cases h1 : InPar a (y₀⁻¹ * γ * y₀)
  · rw [key]
    have hδ₁ : InPar a δ₁ := inPar_conj_adjoin a n γ y₀ δ hA h1
    have hin : InPar a (p⁻¹ * δ₁ * gal (s : F' →+* F') n p) := by
      rw [← hH]
      exact H.mul_mem (H.mul_mem (H.inv_mem ((hH p).2 hp)) ((hH _).2 hδ₁))
        ((hH _).2 (inPar_gal _ a n p hp))
    rw [if_pos hin, if_pos h1]
    obtain ⟨et, eb⟩ := blocks_twist (s : F' →+* F') a b n hn p δ₁ hp hδ₁
    have hN₁ : nrm s δ₁ = incl F F' n (y₀⁻¹ * γ * y₀) := by
      rw [hδ₁def, nrm_conj_incl, hN, map_mul, map_mul, map_inv]
    obtain ⟨nt, nb⟩ := GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks F F' s hs a b n hn _ δ₁ h1 hδ₁ hN₁
    have lα := GlobalTheory.T.base_change_lift_class_function F F' s hs a α hα
    have lβ := GlobalTheory.T.base_change_lift_class_function F F' s hs b β hβ
    rw [et, eb]
    have eα := lα.2 (tlG a δ₁) (tlG a p)
    have eβ := lβ.2 (brG a b δ₁) (brG a b p)
    rw [galAct_apply] at eα eβ
    rw [eα, eβ, lα.1 _ _ (by unfold IsNorm; rw [nt]), lβ.1 _ _ (by unfold IsNorm; rw [nb])]
  · rw [if_neg h1, if_neg]
    intro hin
    obtain ⟨y₁, p₁, hp₁, e, hγ₁⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n hle γ δ (c * p) hA hN).1 hin
    have hh : incl F F' n (y₁⁻¹ * y₀) = p₁ * p⁻¹ := by
      rw [map_mul, map_inv, ← hc, show c = incl F F' n y₁ * p₁ * p⁻¹ by rw [← e]; group]
      group
    have hP : InPar a (y₁⁻¹ * y₀) := by
      rw [← inPar_incl (F' := F'), hh, ← hH]
      exact H.mul_mem ((hH _).2 hp₁) (H.inv_mem ((hH _).2 hp))
    apply h1
    have : y₀⁻¹ * γ * y₀ = (y₁⁻¹ * y₀)⁻¹ * (y₁⁻¹ * γ * y₁) * (y₁⁻¹ * y₀) := by group
    rw [this, ← hH₀]
    exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem ((hH₀ _).2 hP)) ((hH₀ _).2 hγ₁)) ((hH₀ _).2 hP)

theorem pointwise (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) :
    hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n δ = hc a b α β n γ := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  obtain ⟨H, -, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  set T : GL (Fin n) F' → ℂ := fun y => if InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) then
      shLift s α (tlG a (y⁻¹ * δ * gal (s : F' →+* F') n y)) *
      shLift s β (brG a b (y⁻¹ * δ * gal (s : F' →+* F') n y)) else 0 with hTdef
  set c₀ : GL (Fin n) F → ℂ := fun y₀ => if InPar a (y₀⁻¹ * γ * y₀) then
      α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0 with hc₀
  have hsupp : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = incl F F' n k * p := by
    intro y hy
    have hin : InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) := by
      by_contra h; exact hy (if_neg h)
    obtain ⟨k, p, hp, e, -⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n (by omega) γ δ y hA hN).1 hin
    exact ⟨k, p, (hH p).2 hp, e⟩
  have hcnt := count (incl F F' n) H T hsupp
  have hterm : ∀ k (p : H), T (incl F F' n k * p) = c₀ k := fun k p =>
    term F F' s hs a b n hn α β hα hβ γ δ hA hN k p ((hH p).1 p.2)
  simp only [hterm] at hcnt
  have e1 : Nat.card (H.comap (incl F F' n)) = Nat.card {p : GL (Fin n) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.mem_comap, hH, inPar_incl])
  have e2 : Nat.card H = Nat.card {p : GL (Fin n) F' // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hH x)
  have hpos1 : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    rw [← e1]; exact_mod_cast (Nat.card_pos (α := H.comap (incl F F' n))).ne'
  have hpos2 : (Nat.card {p : GL (Fin n) F' // InPar a p} : ℂ) ≠ 0 := by
    rw [← e2]; exact_mod_cast (Nat.card_pos (α := H)).ne'
  haveI := Fintype.ofFinite H
  have hconst : ∀ k, ∑ᶠ _p : H, c₀ k = (Nat.card H : ℂ) * c₀ k := by
    intro k; rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp only [hconst] at hcnt
  rw [← mul_finsum] at hcnt
  have hhc : hc a b α β n γ = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ * ∑ᶠ y₀, c₀ y₀ := by
    simp only [hc, hcTw, gal_id, hc₀]
  rw [hhc, e1, e2] at *
  unfold hcTw
  rw [← hTdef]
  field_simp
  linear_combination hcnt

end GlobalTheory.Shin.LiftHc

theorem GlobalTheory.Shin.shLift_hc_eq_hcTw : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  intro F F' _ _ _ _ s hs a b n hn α β hα hβ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  funext δ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  obtain ⟨y, hyA, hyN⟩ := GlobalTheory.T.conjugate_into_adjoined_algebra F F' s hs n δ γ hγ
  have hcl := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.1
  have hL := (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).2 δ y
  have hR := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F' (s : F' →+* F') a b n (shLift s α) (shLift s β)).1 δ y
  rw [← hL, ← hR, (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).1 _ γ (by unfold IsNorm; rw [hyN])]
  exact (GlobalTheory.Shin.LiftHc.pointwise F F' s hs a b n hn α β hα hβ γ _ hyA hyN).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEq
section
open IsLocalRing Polynomial

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange : ∀ (B₁ B₂ D₁ : Type) [CommRing B₁] [CommRing B₂] [CommRing D₁] [Algebra B₁ B₂] [Algebra B₁ D₁]
    (q : ℕ), 0 < q → ∀ (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[B₁] D₁)),
    GlobalTheory.KeyOriginCut.IsZTorsor B₁ D₁ q act₁ →
    ∃ act₂ : Multiplicative (ZMod q) →* (TensorProduct B₁ B₂ D₁ ≃ₐ[B₂] TensorProduct B₁ B₂ D₁),
      GlobalTheory.KeyOriginCut.IsZTorsor B₂ (TensorProduct B₁ B₂ D₁) q act₂ := by
  intro B₁ B₂ D₁ _ _ _ _ _ q hq act₁ h
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  let act₂ : Multiplicative (ZMod q) →* (B₂ ⊗[B₁] D₁ ≃ₐ[B₂] B₂ ⊗[B₁] D₁) :=
    { toFun := fun g => Algebra.TensorProduct.congr AlgEquiv.refl (act₁ g)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      map_mul' := by
        intro g h
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy] }
  refine ⟨act₂, inferInstance, inferInstance, inferInstance, ?_⟩
  let e₀ := LinearEquiv.ofBijective (Algebra.TensorProduct.productMap
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun _ => AlgHom.id B₁ D₁))
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun g => (act₁ g).toAlgHom))).toLinearMap hbij
  have key : ∀ z : B₂ ⊗[B₁] (D₁ ⊗[B₁] D₁),
      Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))
        (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁ z) =
      TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)
        (LinearEquiv.baseChange B₁ B₂ _ _ e₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add] at hx hy ⊢; rw [hx, hy]
      | tmul x y =>
        funext g
        simp [act₂, e₀, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.piRight_apply,
          Algebra.TensorProduct.congr_apply]
        congr 1
  have hfun : ⇑(Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))) =
      ⇑(TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)) ∘
        ⇑(LinearEquiv.baseChange B₁ B₂ _ _ e₀) ∘
        ⇑(TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [← key, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (TensorProduct.piRight B₁ B₂ B₂ _).bijective.comp
    ((LinearEquiv.baseChange B₁ B₂ _ _ e₀).bijective.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm.bijective)

theorem exists_stage_torsor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq q hq hqu D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ :=
    GlobalTheory.T.spread_torsor_to_etale_algebra T O P φ hφ hSH.2.2.2 q hq D act hD
  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.comap_maximalIdeal (R := Polynomial T) (I := P)

  have hunit : ∀ y : Q.primeCompl, IsUnit (ψ.toRingHom (y : E)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : E) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap E (Localization.AtPrime Q)) = ψ.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) E (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact ψ.comp_algebraMap
  have hjT : ∀ t : T, j (algebraMap T (Localization.AtPrime Q) t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply T (Polynomial T) O, ← RingHom.comp_apply, hjR]
  have hM : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap j := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hjT t).symm⟩
  let ψ' : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.map (GlobalTheory.LocAcyc.GenFib T O) j hM
  have hψ' : ψ'.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j := IsLocalization.map_comp hM

  have hM' : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)).comap
        (algebraMap E (Localization.AtPrime Q)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q) t).symm⟩
  let m : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) :=
    IsLocalization.map _ (algebraMap E (Localization.AtPrime Q)) hM'
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := m.toAlgebra
  obtain ⟨act₂, h₂⟩ := torsor_baseChange (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) DE q hq actE hDE
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, ψ', hψ', _, inferInstance, inferInstance, act₂, h₂, ?_⟩
  intro σ hσ
  refine hred (σ.comp (Algebra.TensorProduct.includeRight (R := GlobalTheory.LocAcyc.GenFib T E)
    (A := GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (B := DE)).toRingHom) fun e => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)), ← RingHom.comp_apply σ, hσ]
  change ψ' (m (algebraMap E _ e)) = _
  simp only [m, IsLocalization.map_eq]
  rw [← RingHom.comp_apply ψ', hψ', RingHom.comp_apply, ← RingHom.comp_apply j, hjE]
  rfl

end GlobalTheory.KeyOriginCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitary
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TorusFrame

theorem sum_angles {r : ℕ} (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ (Fin.castSucc i) = φ ⟨i, by simpa using i.isLt⟩ := by
      intro i; unfold angles; rw [dif_pos (by simpa using i.isLt)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dif_neg (by simp)]
    rw [h2, Finset.sum_congr rfl (fun i _ => h1 i)]
    simp

theorem hermC_eq_dot {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  simp only [hermC, dotProduct, mulVec, map_apply, Finset.mul_sum, mul_assoc]

theorem conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => (starRingEnd ℂ) ((M *ᵥ w) b)) = M.map (starRingEnd ℂ) *ᵥ fun b => (starRingEnd ℂ) (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem hermC_mulVec {r : ℕ} {E : Type} [Field E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * G.map τ * M.map (starRingEnd ℂ)) *ᵥ fun b => (starRingEnd ℂ) (w b)) := by
  rw [hermC_eq_dot, conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_phase {r : ℕ} (φ : Fin (r - 1) → ℝ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).det = 1 := by
  rw [det_diagonal, ← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, sum_angles]
  simp

theorem phase_gram {r : ℕ} (φ : Fin (r - 1) → ℝ) (s : Fin r → ℂ) :
    (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ))))ᵀ * diagonal s *
      (diagonal (fun a => Complex.exp (Complex.I * (angles φ a : ℂ)))).map (starRingEnd ℂ) = diagonal s := by
  rw [diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_conj, mul_comm (Complex.exp _) (s a), mul_assoc, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem torusGL_mem_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ), torusGL hx θ ∈ realSU X.Ψ X.Gm := by
  intro E _ _ _ r X x hx θ
  intro τ
  have hu := isUnit_det_of_isOrth hx τ
  rw [torusGL_val]
  refine ⟨?_, fun u w => ?_⟩
  · rw [det_mul, det_mul, det_phase, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hu]
  · rw [hermC_mulVec, hermC_eq_dot]
    congr 2
    have hG := hx τ
    rw [gram_eq] at hG
    have h1 : (mat x τ)⁻¹ᵀ * (mat x τ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (mat x τ).map (starRingEnd ℂ) * ((mat x τ)⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGτ : X.Gm.map τ.1 = (mat x τ)⁻¹ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        ((mat x τ)⁻¹).map (starRingEnd ℂ) := by
      rw [Matrix.mul_assoc _ _ ((mat x τ)⁻¹.map _), Matrix.mul_assoc _ ((mat x τ).map _), h2, Matrix.mul_one,
        ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hG] at hGτ
    simp only [transpose_mul, Matrix.map_mul]
    rw [hGτ]
    have h1' : (mat x τ)ᵀ * (mat x τ)⁻¹ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h2' : ((mat x τ)⁻¹).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    have key := fun (Q : Matrix (Fin r) (Fin r) ℂ) =>
      (show (diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ)))ᵀ *
          ((diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          ((diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))).map (starRingEnd ℂ) * Q)) =
          (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * Q by
        simp only [← Matrix.mul_assoc, phase_gram])
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat x τ)ᵀ, h1', Matrix.one_mul, ← Matrix.mul_assoc ((mat x τ)⁻¹.map _), h2',
      Matrix.one_mul, key]

end GlobalTheory.TorusFrame
end
end

