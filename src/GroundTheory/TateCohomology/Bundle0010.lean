import Mathlib
import GroundTheory.TateCohomology.Bundle0008
import GroundTheory.TateCohomology.Bundle0006
import GroundTheory.TateCohomology.CupTateShift
import GroundTheory.TateCohomology.CoresRes
import GroundTheory.TateCohomology.Bundle0005

-- bundled from GroundTheory.TateCohomology.CohTrivialPGroup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

section Helpers

universe u

variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}

theorem hom_nsmul_apply (f : A ⟶ B) (n : ℕ) (x : A) : f.hom (n • x) = n • f.hom x :=
  map_nsmul f.hom.toLinearMap n x

theorem hom_zero_apply (f : A ⟶ B) : f.hom 0 = 0 :=
  map_zero f.hom.toLinearMap

end Helpers

variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]

theorem isZero_tateCohomology_of_nsmul_injective {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) (A : Rep ℤ H) (n : ℤ)
    (hinj : Function.Injective fun x : tateCohomology A n => p • x) :
    IsZero (tateCohomology A n) := by
  obtain ⟨m, hm⟩ := hH.exists_card_eq
  have hcard : Fintype.card H = p ^ m := by rw [← Nat.card_eq_fintype_card, hm]
  have key : ∀ (j : ℕ) (x : tateCohomology A n), p ^ j • x = 0 → x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      apply ih
      apply hinj
      change p • (p ^ j • x) = p • 0
      rw [smul_zero, ← mul_smul, ← pow_succ']
      exact hx
  have : Subsingleton (tateCohomology A n) :=
    ⟨fun x y => by
      rw [key m x (hcard ▸ card_smul_tateCohomology A n x),
        key m y (hcard ▸ card_smul_tateCohomology A n y)]⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem tateAcyclic_of_shortExact_of_comp_eq_nsmul {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) {S : ShortComplex (Rep ℤ H)} (hS : S.ShortExact) (e : S.X₂ ≅ S.X₁)
    (hf : S.f ≫ e.hom = p • 𝟙 S.X₁) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ := by
  intro n
  have hmono : Mono ((tateCohomologyFunctor n).map S.f) := by
    have h : Mono ((tateCohomologyFunctor (n - 1 + 1)).map S.f) :=
      (TateCohomology.exact₁ hS (n - 1)).mono_g ((h₃ (n - 1)).eq_of_src _ _)
    rwa [sub_add_cancel] at h
  have : (tateCohomologyFunctor (R := ℤ) (G := H) n).Additive := by
    unfold tateCohomologyFunctor; infer_instance
  have hmono' : Mono ((tateCohomologyFunctor n).map (p • 𝟙 S.X₁)) := by
    rw [← hf, Functor.map_comp]
    infer_instance
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hmono'
  have hinj := (ModuleCat.mono_iff_injective _).1 hmono'
  refine isZero_tateCohomology_of_nsmul_injective hH S.X₁ n fun a b hab => hinj ?_
  simpa using hab

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion (hG : IsPGroup p G)
    (A : Rep ℤ G) (hA : ∀ x : A, p • x = 0 → x = 0) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let f : A ⟶ A := p • 𝟙 A
  have hf : Function.Injective f.hom := fun a b hab => by
    have h : p • (a - b) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [f, nsmul_id_hom_apply] using hab
    exact sub_eq_zero.mp (hA _ h)
  have : Mono f := (Rep.mono_iff_injective f).2 hf
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
      mono_f := inferInstanceAs (Mono f)
      epi_g := coequalizer.π_epi }
  have hC : IsZero (tateCohomology S.X₃ q) :=
    (TateCohomology.exact₃ hS q).isZero_X₂ (h₁.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  have hCt : ∀ y : S.X₃, p • y = 0 := by
    have hsurj : Function.Surjective (cokernel.π f).hom :=
      (Rep.epi_iff_surjective _).1 coequalizer.π_epi
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have h0 := congrArg (fun φ : A ⟶ cokernel f => φ.hom x) (cokernel.condition f)
    simp only [Rep.hom_comp, Rep.zero_hom] at h0
    rw [← hom_nsmul_apply, ← nsmul_id_hom_apply]
    exact h0
  obtain ⟨tC, cC⟩ := tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero hG S.X₃ hCt q hC
  have hf0 : S.f ≫ (Iso.refl S.X₁).hom = p • 𝟙 S.X₁ := Category.comp_id _
  have t := tateAcyclic_of_shortExact_of_comp_eq_nsmul hG hS (Iso.refl S.X₁) hf0 tC
  refine ⟨t, ?_⟩
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have h₃ : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact cC H
  have hf' : (S.map (resFunctor H.subtype)).f ≫ (Iso.refl (S.map (resFunctor H.subtype)).X₁).hom =
      p • 𝟙 (S.map (resFunctor H.subtype)).X₁ := by
    show (resFunctor H.subtype).map (p • 𝟙 A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have c := tateAcyclic_of_shortExact_of_comp_eq_nsmul (hG.to_subgroup H) hS'
    (Iso.refl (S.map (resFunctor H.subtype)).X₁) hf' h₃
  rw [ShortComplex.map_X₁] at c
  exact c

theorem tateAcyclic_cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    TateAcyclic A ∧ CohTrivial A := by
  let π : Rep.free ℤ G A.V ⟶ A := Rep.freeLift ℤ G A fun a => a
  have hπ : Function.Surjective π.hom := fun a =>
    ⟨Finsupp.single a (MonoidAlgebra.single 1 1), by
      have hmod : A.hV2 = AddCommGroup.toIntModule A.V := Subsingleton.elim _ _
      simp only [π]
      simp
      rw [hmod]
      exact one_zsmul a⟩
  have : Epi π := (Rep.epi_iff_surjective π).2 hπ
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
      mono_f := equalizer.ι_mono
      epi_g := inferInstanceAs (Epi π) }
  have hfree : ∀ x : Rep.free ℤ G A.V, p • x = 0 → x = 0 := fun x hx =>
    (smul_eq_zero.mp hx).resolve_left (Fact.out : p.Prime).ne_zero
  have hK : ∀ x : S.X₁, p • x = 0 → x = 0 := by
    have hinj : Function.Injective (kernel.ι π).hom :=
      (Rep.mono_iff_injective _).1 equalizer.ι_mono
    intro x hx
    apply hinj
    rw [hom_zero_apply]
    apply hfree
    rw [← hom_nsmul_apply, hx, hom_zero_apply]
  have h2 : TateAcyclic S.X₂ := tateAcyclic_free A.V
  have k₁ : IsZero (tateCohomology S.X₁ (q + 1)) :=
    h₁.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS q) (isIso_δ_of_tateAcyclic hS h2 q)).symm
  have k₂ : IsZero (tateCohomology S.X₁ (q + 1 + 1)) :=
    h₂.of_iso (@asIso _ _ _ _ (TateCohomology.δ hS (q + 1))
      (isIso_δ_of_tateAcyclic hS h2 (q + 1))).symm
  obtain ⟨tK, cK⟩ :=
    tateAcyclic_cohTrivial_of_isZero_of_isZero_of_noTorsion hG S.X₁ hK (q + 1) k₁ k₂
  have t3 := TateAcyclic.of_shortExact_X₁ hS h2 tK
  have c2 : CohTrivial S.X₂ := cohTrivial_free A.V
  have c3 := CohTrivial.of_shortExact_X₁ hS c2 cK
  exact ⟨t3, c3⟩

theorem cohTrivial_of_isZero_of_isZero (hG : IsPGroup p G) (A : Rep ℤ G) (q : ℤ)
    (h₁ : IsZero (tateCohomology A q)) (h₂ : IsZero (tateCohomology A (q + 1))) :
    CohTrivial A :=
  (tateAcyclic_cohTrivial_of_isZero_of_isZero hG A q h₁ h₂).2

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.CupTate
section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩

omit [Fintype G] in

theorem cupH_zero_zero_π {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by
  rw [cupH_π]
  congr 1
  apply cocycles_ext
  rw [iCocycles_cupCocycles, iCocycles_mk, iCocycles_mk, iCocycles_mk]
  funext v
  rw [cupCochain_apply, h]
  have hv : ∀ w : Fin 0 → G, w = v := fun w => Subsingleton.elim _ _
  rw [hv (fun i : Fin 0 => v ⟨i, by omega⟩), hv (fun j : Fin 0 => v ⟨0 + j, by omega⟩)]
  simp [Fin.partialProd]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem tateCup_zero_zero (A B : Rep.{u} k G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tateCup 0 0 A B 0 (add_zero 0)
        (((tateCohomologyZeroIso k G).app A).inv.hom (Submodule.Quotient.mk x))
        (((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y)) =
      ((tateCohomologyZeroIso k G).app (A ⊗ B)).inv.hom
        (Submodule.Quotient.mk (tensorInvariants x y)) := by
  obtain ⟨zA, hzA⟩ := exists_tateComplex_cycles_zero A x
  obtain ⟨zB, hzB⟩ := exists_tateComplex_cycles_zero B y
  obtain ⟨zAB, hzAB⟩ := exists_tateComplex_cycles_zero (A ⊗ B) (tensorInvariants x y)
  rw [tateCohomologyZeroIso_inv_mk A zA x hzA.symm, tateCohomologyZeroIso_inv_mk B zB y hzB.symm,
    tateCohomologyZeroIso_inv_mk (A ⊗ B) zAB _ hzAB.symm]
  rw [tateCup_of_nonpos 0 le_rfl]
  apply moduleIso_hom_injective (tateLeftIso A B 0)
  rw [tateLeftIso_cupL, tateCup_of_pos_of_nonpos (by norm_num) le_rfl]
  apply moduleIso_hom_injective (tateRightIso (augIdeal k G ⊗ A) B (0 + 1))
  rw [tateRightIso_cupR]
  apply moduleIso_hom_injective (tateIsoH ((augIdeal k G ⊗ A) ⊗ (augIdeal k G ⊗ B)) (0 + 1 + 1) 2
    (by norm_num))
  have hA1 := tateIsoH_tδ_homologyπ (augSES_shortExact A) 0 zA
  have hB1 := tateIsoH_tδ_homologyπ (augSES_shortExact B) 0 zB
  have hAB1 := tateIsoH_tδ_homologyπ (augSES_tensorRight_shortExact A B) 0 zAB
  have hxA : ∀ v, ((tateComplex A).iCycles 0).hom zA v = x.1 := fun v => congrFun hzA v
  have hyB : ∀ v, ((tateComplex B).iCycles 0).hom zB v = y.1 := fun v => congrFun hzB v
  have hxyAB : ∀ v, ((tateComplex (A ⊗ B)).iCycles 0).hom zAB v = x.1 ⊗ₜ[k] y.1 :=
    fun v => congrFun hzAB v
  have hcup0 := cupH_zero_zero_π _ _ (tate_d_iCycles A 0 zA) (tate_d_iCycles B 0 zB) _
    (tate_d_iCycles (A ⊗ B) 0 zAB)
    (fun v => (hxyAB v).trans (congrArg₂ (fun a b => a ⊗ₜ[k] b) (hxA v).symm (hyB v).symm))
  have e_left := δ_cupH_left (augSES_shortExact A) B (augSES_tensorRight_shortExact A B)
    (p := 0) (q := 0) rfl rfl
    (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA)))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_right := δ_cupH_right (augSES_shortExact B) (augIdeal k G ⊗ A)
    (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) (p := 0) (q := 1) rfl rfl
    (δ (augSES_shortExact A) 0 (0 + 1) rfl
      (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA))))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_br := congr(($(tδ_comp_tateIsoH (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1)).hom
    ((tateLeftIso A B 0).hom.hom (((tateComplex (A ⊗ B)).homologyπ 0).hom zAB)))
  have e_base := tateIsoH_tateCup (n := 1) (m := 1) (l := 2) (p := 0 + 1) (q := 0 + 1) (r := 0 + 1 + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (augIdeal k G ⊗ A) (augIdeal k G ⊗ B) ((augShiftδ A 0).hom (((tateComplex A).homologyπ 0).hom zA))
    ((augShiftδ B 0).hom (((tateComplex B).homologyπ 0).hom zB))
  refine Eq.trans (moduleHom_smul _ _ _) ?_
  refine Eq.trans (congrArg (tsgn k (0 + 1) • ·) e_base) ?_
  refine Eq.trans (congrArg₂ (fun s t => tsgn k (0 + 1) • cupH (show 1 + 1 = 2 by rfl) s t)
    hA1 hB1) ?_
  refine Eq.trans ?_ e_br.symm
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1 (1 + 1)
    rfl).hom hAB1).symm
  refine Eq.trans ?_ (congrArg (fun t => δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl (δ (augSES_tensorRight_shortExact A B) 0 (0 + 1) rfl t)) hcup0)
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl).hom e_left).symm
  refine Eq.trans ?_ e_right.symm
  have hs : tsgn k (0 + 1) = (-1 : k) ^ 1 := by
    rw [tsgn_add_one]
    simp [tsgn]
  rw [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem tateCup_unique_of_agrees (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]

noncomputable def tateCupTensor (A B : Rep.{u} k G) (p q : ℤ) :
    TensorProduct k (tateCohomology A p) (tateCohomology B q) →ₗ[k] tateCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (tateCup p q A B (p + q) rfl)

theorem tateCup_δ_left {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b :=
  tateCup_connecting_left _ p q rfl hE B hEB r h a b

theorem tateCup_δ_right {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.ResCoresZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

section Invariants

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

def invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) : (res f A).ρ.invariants :=
  ⟨x, fun h => x.2 (f h)⟩

@[simp]
lemma coe_invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) :
    (invariantsRes f x : A) = x := rfl

variable (S : Subgroup G) {A : Rep.{u} k G}

lemma ρ_mul_of_mem (y : (res S.subtype A).ρ.invariants) (g : G) {s : G} (hs : s ∈ S) :
    A.ρ (g * s) (y : A) = A.ρ g y := by
  rw [map_mul, Module.End.mul_apply]
  exact congrArg (A.ρ g) (y.2 ⟨s, hs⟩)

def cosetSMul (y : (res S.subtype A).ρ.invariants) (q : G ⧸ S) : A :=
  Quotient.liftOn' q (fun g => A.ρ g y) fun g g' h => by
    rw [QuotientGroup.leftRel_apply] at h
    rw [← ρ_mul_of_mem S y g h, mul_inv_cancel_left]

@[simp]
lemma cosetSMul_mk (y : (res S.subtype A).ρ.invariants) (g : G) :
    cosetSMul S y (g : G ⧸ S) = A.ρ g y := rfl

lemma cosetSMul_smul (y : (res S.subtype A).ρ.invariants) (h : G) (q : G ⧸ S) :
    cosetSMul S y (h • q) = A.ρ h (cosetSMul S y q) := by
  induction q using QuotientGroup.induction_on with | H g =>
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, cosetSMul_mk, cosetSMul_mk, map_mul,
    Module.End.mul_apply]

variable [Fintype G]

open scoped Classical in

noncomputable def transferSum (y : (res S.subtype A).ρ.invariants) : A :=
  ∑ q : G ⧸ S, cosetSMul S y q

lemma transferSum_mem_invariants (y : (res S.subtype A).ρ.invariants) :
    transferSum S y ∈ A.ρ.invariants := fun h => by
  classical
  simp only [transferSum, map_sum]
  rw [show (∑ q : G ⧸ S, A.ρ h (cosetSMul S y q)) = ∑ q : G ⧸ S, cosetSMul S y (h • q) from
    Finset.sum_congr rfl fun q _ => (cosetSMul_smul S y h q).symm]
  exact Fintype.sum_equiv (MulAction.toPerm h) _ _ fun _ => rfl

noncomputable def transferInv (y : (res S.subtype A).ρ.invariants) : A.ρ.invariants :=
  ⟨transferSum S y, transferSum_mem_invariants S y⟩

@[simp]
lemma coe_transferInv (y : (res S.subtype A).ρ.invariants) :
    (transferInv S y : A) = transferSum S y := rfl

end Invariants

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

def coindConst (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (coind S.subtype B).ρ.invariants :=
  ⟨⟨fun _ => y, (Representation.mem_coindV _ _ _).2 fun s _ => (y.2 s).symm⟩,
    fun _ => rfl⟩

@[simp]
lemma coindConst_apply (B : Rep.{u} k S) (y : B.ρ.invariants) (g : G) :
    ((coindConst S B y : coind S.subtype B) : G → B) g = y := rfl

variable [Fintype G] [Fintype S]

lemma homologyMap_tateShapiroMap_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (HomologicalComplex.homologyMap (tateShapiroMap S B) 0).hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) :=
  homologyMap_tateZeroClass _ y _ (funext fun v => Subtype.ext (funext fun g =>
    shapiroCochains_hom_f_zero_const S B y y.2 v g))

lemma tateCoindIso_inv (B : Rep.{u} k S) (n : ℤ) :
    (tateCoindIso S B n).inv = HomologicalComplex.homologyMap (tateShapiroMap S B) n := by
  refine (cancel_mono (tateCoindIso S B n).hom).1 ?_
  exact (Iso.inv_hom_id _).trans (homologyMap_tateShapiroMap_comp_tateCoindIso_hom S B n).symm

theorem tateCoindIso_hom_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).hom.hom (tateZeroClass (coind S.subtype B) (coindConst S B y)) =
      tateZeroClass B y := by
  rw [← homologyMap_tateShapiroMap_tateZeroClass, ← tateCoindIso_inv]
  exact Iso.inv_hom_id_apply (tateCoindIso S B 0) _

theorem tateCoindIso_inv_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).inv.hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) := by
  rw [tateCoindIso_inv]
  exact homologyMap_tateShapiroMap_tateZeroClass S B y

end Shapiro

section ResCores

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem tateRes_tateZeroClass (A : Rep.{u} k G) (x : A.ρ.invariants) :
    ((tateRes S 0).app A).hom (tateZeroClass A x) =
      tateZeroClass (res S.subtype A) (invariantsRes S.subtype x) := by
  rw [tateRes_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [tateCohomologyFunctor_map_tateZeroClass]
  have h : ((Rep.invariantsFunctor k G).map
      ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)).hom x =
      coindConst S (res S.subtype A) (invariantsRes S.subtype x) :=
    Subtype.ext (Subtype.ext (funext fun g => x.2 g))
  rw [h]
  exact tateCoindIso_hom_tateZeroClass S (res S.subtype A) (invariantsRes S.subtype x)

omit [Fintype S] in

lemma counit_indCoindIso_inv_coindConst [DecidableRel (QuotientGroup.rightRel S)]
    (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((Rep.indResAdjunction.{u} k S.subtype).counit.app A).hom
      ((indCoindIso (res S.subtype A)).inv.hom (coindConst S (res S.subtype A) y)) =
      transferSum S y := by
  classical
  change ((Rep.indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (coindConst S (res S.subtype A) y)) = _
  rw [coindToInd_apply, map_sum, transferSum]
  refine (Finset.sum_congr (by convert rfl) fun x _ => ?_ : _ = ∑ x : Quotient (QuotientGroup.rightRel S),
    cosetSMul S y (QuotientGroup.quotientRightRelEquivQuotientLeftRel S x)).trans (Equiv.sum_comp _ _)
  induction x using Quotient.inductionOn with
  | h g =>
    rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
    rfl

theorem tateCores_tateZeroClass (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((tateCores S 0).app A).hom (tateZeroClass (res S.subtype A) y) =
      tateZeroClass A (transferInv S y) := by
  classical
  rw [tateCores_app, tateIndIso_inv_eq, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, tateCoindIso_inv_tateZeroClass,
    tateCohomologyFunctor_map_tateZeroClass, tateCohomologyFunctor_map_tateZeroClass]
  congr 1
  exact Subtype.ext (counit_indCoindIso_inv_coindConst S A y)

end ResCores

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateResEqZeroOfNsmulEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateCores_app_tateRes_app_apply (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (n : ℤ)
    (x : tateCohomology A n) :
    ((tateCores S n).app A).hom (((tateRes S n).app A).hom x) = S.index • x := by
  have h := congrArg (fun f => f.hom x) (tateRes_app_comp_tateCores_app S A n)
  simpa using h

end GroundTheory.GroupCoh
end

