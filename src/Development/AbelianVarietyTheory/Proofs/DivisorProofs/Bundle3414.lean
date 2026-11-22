import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

variable {Z : Scheme.{0}}

theorem sf_resG_resG {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem sf_resG_id {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : resG Z h x = x :=
  congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))

theorem sf_resG_inj {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) {x y : Γ(Z, U)}
    (e : resG Z h x = resG Z h y) : x = y := by
  have := congrArg (resG Z h') e
  rwa [sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id] at this

variable {J : Type} (W : J → Z.Opens) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))

def sfCr (U : Z.Opens) (i i' : J) (h : U ≤ W i ⊓ W i') : Γ(Z, U) := resG Z h (c i i')

theorem sfCr_res {U V : Z.Opens} (i i' : J) (h : U ≤ W i ⊓ W i') (h' : V ≤ U) :
    resG Z h' (sfCr W c U i i' h) = sfCr W c V i i' (h'.trans h) :=
  sf_resG_resG _ _ _

theorem sfCr_add (hc : IsCoc W c) (U : Z.Opens) (i i' i'' : J) (h : U ≤ W i ⊓ W i' ⊓ W i'') :
    sfCr W c U i i' (h.trans inf_le_left) +
      sfCr W c U i' i'' (h.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) =
      sfCr W c U i i'' (h.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := by
  have e := congrArg (resG Z h) (hc i i' i'')
  rw [map_add, sf_resG_resG, sf_resG_resG, sf_resG_resG] at e
  exact e

theorem sfCr_self (hc : IsCoc W c) (U : Z.Opens) (i : J) (h : U ≤ W i ⊓ W i) :
    sfCr W c U i i h = 0 := by
  have e := sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))
  have e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h := e
  linear_combination e2

theorem sfCr_congr (U : Z.Opens) {i j i' : J} (e : i = j) (h : U ≤ W i ⊓ W i') (h' : U ≤ W j ⊓ W i') :
    sfCr W c U i i' h = sfCr W c U j i' h' := by subst e; rfl

theorem sfCr_congr2 (U : Z.Opens) {i i' j' : J} (e : i' = j') (h : U ≤ W i ⊓ W i') (h' : U ≤ W i ⊓ W j') :
    sfCr W c U i i' h = sfCr W c U i j' h' := by subst e; rfl

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

theorem cechAffineCochainValue_congr_source (f : C1 (OAff s)) {A A' B : Z.affineOpens} (e : A = A') (h : B.1 ≤ A.1) (h' : B.1 ≤ A'.1) :
    fv s f h = fv s f h' := by subst e; rfl

end GlobalTheory.CechFin

open GlobalTheory.CechPoset in

theorem GlobalTheory.CechFin.cocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  intro R _ Z s J W hW hW2 hI S hS c hc
  let κ := {j // j ∈ S}
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let D : κ → Z.Opens := fun k => W k.1
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k) := by
    classical
    intro I hIn
    have := hI (I.image Subtype.val) (hIn.image _)
    rwa [Finset.iInf_finset_image] at this
  have hcov : ⨆ k, D k = ⊤ := by
    rw [← hS, iSup_subtype']
  have hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1 :=
    fun a b => Finset.iInf_union
  have hsup : ⨆ a, (cov D hD a).1 = ⊤ := by
    refine eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))
    refine le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1)
      (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))
    simp [cov]
  have hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1 :=
    fun a k hk => biInf_le (fun k => D k) hk
  let Fv : C1 (covF s D hD) := fun a b φ =>
    sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1
      (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))
  have hF : Fv ∈ Z1 (covF s D hD) := by
    intro a b d φ ψ
    have e := sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1
      (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b))))
        (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))
    show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ =
      resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) +
        sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _
    rw [sfCr_res]
    rw [add_comm]
    exact e.symm
  obtain ⟨y, hy⟩ := (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2
    (H1.mk _ ⟨Fv, hF⟩)
  obtain ⟨f0, rfl⟩ := H1.mk_surjective _ y
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hy
  obtain ⟨g, hg⟩ := hy

  let hfun : ∀ i, Γ(Z, W i) := fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi =>
      -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm :
        W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1)
        (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)
  refine ⟨-f0, hfun, fun i hi i' hi' => ?_⟩
  let k : κ := ⟨i, hi⟩
  let k' : κ := ⟨i', hi'⟩
  let a := ne {k} (Finset.singleton_nonempty k)
  let a' := ne {k'} (Finset.singleton_nonempty k')
  let b := ne {k, k'} (Finset.insert_nonempty k {k'})
  have ca : (cov D hD a.unop).1 = W i := Finset.iInf_singleton k D
  have ca' : (cov D hD a'.unop).1 = W i' := Finset.iInf_singleton k' D
  have cb : (cov D hD b.unop).1 = W i ⊓ W i' := by
    show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  let φ : a ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))
  let φ' : a' ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))
  have hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1 := cov_mono D hD (leOfHom φ.unop)
  have ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1 := cov_mono D hD (leOfHom φ'.unop)
  have hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i' := cb.le
  have hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1 := cb.ge
  have mna : mn a = k := Finset.min'_singleton k
  have mna' : mn a' = k' := Finset.min'_singleton k'
  have hxB : (cov D hD b.unop).1 ≤ W (mn b).1 := hmem b _ (mn_mem b)
  have h4 := congrFun (congrFun (congrFun hg a) b) φ
  have h5 := congrFun (congrFun (congrFun hg a') b) φ'
  have h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A := cov D hD a.unop) (B := cov D hD b.unop) hab -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]
    exact h4
  have h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A := cov D hD a'.unop) (B := cov D hD b.unop) ha'b -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]
    exact h5
  have c1 := sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i'
    (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))
  have c2 := sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1
    (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)
  rw [sfCr_self W c hc] at c2
  have r1 := res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_left hBP
  have r2 := res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_right hBP
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab] at r1
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b] at r2
  have erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') =
      -resG Z hBP (fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) +
        resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by
    show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
      -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) = _
    rw [map_sub, map_neg, map_neg]; ring
  have e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP := rfl
  have t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a) := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi]
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  have t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a') := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi']
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  rw [r1, r2] at erho
  apply sf_resG_inj hBP hPB
  rw [map_add, map_sub, t1, t2]
  linear_combination e0 - erho - h4' + h5' - c1 + c2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add, ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add, ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'
    rw [map_add, map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ, ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) = algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  first | exact @GlobalTheory.FracPt.chart_eq_value_mul_pow | exact GlobalTheory.FracPt.chart_eq_value_mul_pow | (intros; apply GlobalTheory.FracPt.chart_eq_value_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionRelOfTranslateSectionValuesStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunction_rel_of_translate_section_values : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.HeatTrans.chart_rel_of_sval | exact GlobalTheory.HeatTrans.chart_rel_of_sval | (intros; apply GlobalTheory.HeatTrans.chart_rel_of_sval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartUniformBoundStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_uniform_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  first | exact @GlobalTheory.MetFam.exists_bound_chernPart_univ | exact GlobalTheory.MetFam.exists_bound_chernPart_univ | (intros; apply GlobalTheory.MetFam.exists_bound_chernPart_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChoiceFreeSectionConstruction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem nef_big_A : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), FnAlgClosed Xo c → WtBig P → IsNef c.F (h.geo f₁ f₂ th k).LA ∧ IsBig c.F (h.geo f₁ f₂ th k).LA := by
  intro hP hN hS hC hL E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k hF hW
  obtain ⟨hsm, hpr, hgc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have hsm' : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) (str₀ TF.X Z)
  haveI : IsIntegral (Y₀ TF.X Z) := isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  set la : AllWt.Weight Dw := P.u₂ + dimFlag Dw • P.u₁ with hla
  have hg₁ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₁ (by simp)).1
  have hg₂ := (GlobalTheory.HSApp.gaps_of_wtBig E H Dw P hW P.u₂ (by simp)).1
  have hgla : GapGe 1 la := by
    intro τ k hk
    have a₁ := hg₁ τ k hk
    have a₂ := hg₂ τ k hk
    simp only [hla, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
    nlinarith
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hf₀ : ∀ r : c.F, algebraMap c.F Γ(Y₀ TF.X Z, ⊤) r =
      (str₀ TF.X Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hs₀ : strHom c.F (Y₀ TF.X Z) = str₀ TF.X Z := strHom_eq hf₀
  have hp₀ : IsProjOver (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hpr
  obtain ⟨hprop₀, H₀, hH₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpr
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => GlobalTheory.T.nef_line_bundle_weight_gap hP hN hL E H Dw l Xo c TF Z hF w hw
  have nef₀ : IsNef c.F (L₀ TF.X Z la) := nef la (hgla.mono (by norm_num))
  have big₀ : IsBig c.F (L₀ TF.X Z la) := by
    obtain ⟨y₀⟩ : Nonempty (Y₀ TF.X Z) := by
      obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
      obtain ⟨y, -⟩ := (str₀ TF.X Z).surjective z
      exact ⟨y⟩
    have hne : (U₀ TF.X Z : Set (Y₀ TF.X Z)).Nonempty := (dense_U₀ TF.X Z).nonempty
    obtain ⟨y, hy⟩ := hne
    obtain ⟨mu, hmu0, m, hm, hA⟩ := GlobalTheory.T.ample_line_bundle_weight_gap hP hN hS hC E H Dw l Xo c TF Z hF la hgla y hy
    obtain ⟨m', Aa, s, hm', hAa, hAamp, hys⟩ := hA
    have hNn := isLB_L₀ TF.X Z (m • la - mu)
    have hdiv : (LB.div (lbPow (L₀ TF.X Z (m • la - mu)) m') Aa).IsLB := Semi.LB.isLB_div (isLB_lbPow hNn m') hAa
    have nefmu := nef mu hmu0
    have hB := (nefmu.pow hAamp m').isBig_tens_ample hN hp₀ hAamp
    have hcls0 : cls (L₀ TF.X Z 0) (isLB_L₀ TF.X Z 0) = 0 := by
      have h := cls_common_add (common₀ TF.X Z) 0 0
      simp only [add_zero] at h
      exact left_eq_add.1 h
    have hnsmul : ∀ n : ℕ, cls (L₀ TF.X Z (n • la)) (isLB_L₀ TF.X Z _) = n • cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) := by
      intro n
      induction n with
      | zero => simpa only [zero_nsmul] using hcls0
      | succ n ih => rw [succ_nsmul, cls_common_add (common₀ TF.X Z), ih, succ_nsmul]
    have h1 := cls_common_add (common₀ TF.X Z) (m • la - mu) mu
    rw [sub_add_cancel] at h1
    have hP' := isLB_lbPow (isLB_L₀ TF.X Z la) (m * m')
    have e : cls (lbPow (L₀ TF.X Z la) (m * m')) hP' = cls _ hB.isLB + cls _ hdiv := by
      rw [cls_lbPow (isLB_L₀ TF.X Z la), cls_tens (isLB_lbPow nefmu.isLB m') hAa, cls_div (isLB_lbPow hNn m') hAa,
        cls_lbPow nefmu.isLB, cls_lbPow hNn, mul_nsmul, ← hnsmul m, h1, smul_add]
      abel
    have hbigP : IsBig c.F (lbPow (L₀ TF.X Z la) (m * m')) :=
      hB.of_cls_eq_add hf₀ hpr hdiv ⟨s, sec_ne_zero_of_mem hys⟩ hP' e
    exact hbigP.of_pow (isLB_L₀ TF.X Z la) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' hm'.ne'))
      (fun j => finite_coh_zero_twist_of_isProjOver hf₀ hpr (isLB_lbPow (isLB_L₀ TF.X Z la) j))
  have bigpull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X → Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) → (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := fun k _ X Y _ p g hp hd hg N hN => GlobalTheory.BigPull.isBig_pull k X Y p g hp hd hg N hN
  obtain ⟨hprop₁, H₁, hH₁⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 R.proj
  haveI : IsProper (strHom c.F (Y₀ TF.X Z)) := hs₀ ▸ hprop₀
  haveI : IsProper (R.σ ≫ str₀ TF.X Z) := hprop₁
  haveI : IsProper R.σ := IsProper.of_comp R.σ (str₀ TF.X Z)
  have hcl : IsClosedMap R.σ := Scheme.Hom.isClosedMap R.σ
  haveI : Nonempty R.X := by
    obtain ⟨z⟩ : Nonempty (Sp c.F) := inferInstance
    haveI : GeometricallyConnected R.str := h.conn
    obtain ⟨y, -⟩ := R.str.surjective z
    exact ⟨y⟩
  haveI : Nonempty (Y₀ TF.X Z) := ⟨R.σ (Classical.arbitrary R.X)⟩
  have hdim : topologicalKrullDim R.X = topologicalKrullDim (Y₀ TF.X Z) := by
    rw [GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth R.str (dimFlag Dw) R.smooth,
      GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (str₀ TF.X Z) (dimFlag Dw) hsm]
  have hdense : Dense (Set.range R.σ) := by
    refine (dense_U₀ TF.X Z).mono fun y hy => ?_
    have := R.iso
    obtain ⟨x, hx⟩ := (R.σ ∣_ U₀ TF.X Z).surjective ⟨y, hy⟩
    refine ⟨(R.σ ⁻¹ᵁ U₀ TF.X Z).ι x, ?_⟩
    have e := congrArg (fun q => q x) (morphismRestrict_ι R.σ (U₀ TF.X Z))
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e, hx]
    rfl
  letI := algebraΓOfHom R.str
  change IsNef c.F ((L₀ TF.X Z la).pull R.σ) ∧ IsBig c.F ((L₀ TF.X Z la).pull R.σ)
  exact ⟨GlobalTheory.PosBaseChange.isNef_pull nef₀ hH₀ hH₁ R.σ hcl,
    bigpull c.F (Y₀ TF.X Z) R.X (str₀ TF.X Z) R.σ R.proj hdim hdense _ big₀⟩

end GlobalTheory.HSApp
end

