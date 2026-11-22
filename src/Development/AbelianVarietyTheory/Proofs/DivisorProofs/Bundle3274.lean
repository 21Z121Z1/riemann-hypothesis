import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3257
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyGenericFibre
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.Published
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier

namespace GlobalTheory.FibreProj

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem dim_closure_lt (hB : IsArithVar q d) {b : B} (hb : b ≠ genericPoint B) :
    topologicalKrullDim (closure ({b} : Set B)) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
  have hgen : genericPoint B ∉ closure ({b} : Set B) := fun h =>
    hb ((genericPoint_specializes b).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
  have h1 : topologicalKrullDim (Set.univ : Set B) = (d + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hB.dim_eq
  have hup : topologicalKrullDim (closure ({b} : Set B)) + 1 ≤ (d + 1 : ℕ) :=
    h1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint B, trivial, hgen, genericPoint_specializes x⟩
  by_contra h
  have := (add_le_add_left (not_lt.1 h) 1).trans hup
  norm_cast at this
  omega

theorem interNum_eq_zero_of_ne [IsIntegral Y] {f : Y ⟶ B} {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) (hf : f (genericPoint Y) ≠ genericPoint B)
    {ι : Type} [Fintype ι] {P : ι → LB G} (hP : ∀ i, (P i).IsLB) :
    (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P) = 0 := by
  obtain ⟨-, h₂, -, h₄⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
  have : IsEmpty G := not_nonempty_iff.1 fun hG => by
    obtain ⟨_, e⟩ := h₄ hG
    exact hf (h₂.le ⟨_, e⟩)
  letI := algebraΓOfHom s
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _) hP

theorem ne_genericPoint_of_vertical (hB : IsArithVar q d) {Z : Scheme.{0}} (g : Z ⟶ B) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] (z : Z) : g z ≠ genericPoint B := fun e => by
  have := hB.charZero
  have h₁ : genericPoint B ∈ B.basicOpen (l : Γ(B, ⊤)) :=
    (unitAt_fnOf_iff (Opens.mem_top _) (Opens.mem_top _) _).1 (unitAt_genericPoint
      ((map_ne_zero_iff _ (fnOf_injective ⊤ (Opens.mem_top _))).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)))
  have h₂ : z ∈ g ⁻¹ᵁ B.basicOpen (l : Γ(B, ⊤)) := show g z ∈ _ from e ▸ h₁
  rw [Scheme.preimage_basicOpen_top, map_natCast, ← map_natCast (algebraMap (ZMod l) Γ(Z, ⊤)), ZMod.natCast_self, map_zero,
    Scheme.basicOpen_zero] at h₂
  exact h₂

theorem isProper_of_isArithVar {D : ℕ} (h : IsArithVar p D) : IsProper p := by
  obtain ⟨N, j, _, hj⟩ := h.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem isArFun_pull (H : ArCalc) [IsIntegral Y] (hB : IsArithVar q d) (hY : IsArithVar p d) (f : Y ⟶ B) (w : f ≫ q = p)
    {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) {κ : Type} [Fintype κ] {A : κ → HermLB q}
    {Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) {ι : Type} [Fintype ι] [IsEmpty ι] (P : ι → LB G) :
    IsArFun (fun a => (A a).pull f w) d
      (((letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P : ℤ) : ℝ) • Φ) := by
  by_cases hf : f (genericPoint Y) = genericPoint B
  · obtain ⟨-, h₂, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
    obtain ⟨x, -⟩ : genericPoint Y ∈ Set.range j := h₂.ge hf
    have := isProper_of_isArithVar hB
    have : IsProper (f ≫ q) := w ▸ isProper_of_isArithVar hY
    have : IsProper f := IsProper.of_comp f q
    obtain ⟨h₃, h₄⟩ := GlobalTheory.T.residue_degree_eq_euler_characteristic B Y f G j s h (GlobalTheory.T.generic_fibre_projective k B Y q p hB.isProjOver hY.isProjOver f w G j s h)
      (GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) 0 hB.dim_eq hY.dim_eq.le f G j s h) ⟨x⟩
    letI := algebraΓOfHom s
    rw [interNum_of_isEmpty, h₄]
    exact (H.arProj k B Y q p d hB hY f w hf h₃).2 κ A Φ hΦ
  · rw [interNum_eq_zero_of_ne h hf isEmptyElim, Int.cast_zero, zero_smul]
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    obtain ⟨t, ht, e⟩ := ProjDrop.isSelfInter_zero_of_dim_lt H k B Y q p d d hB hY f w (dim_closure_lt hB hf) (comb A n)
    exact ⟨t, (H.arIso k Y p d hY).1 _ _ t (isometric_comb_pull A n f w).symm ht, e⟩

omit [IsIntegral B] in

theorem isometric_pull_pull {Z : Scheme.{0}} (L : HermLB q) (f : Y ⟶ B) (w : f ≫ q = p) (i : Z ⟶ Y)
    (h : (i ≫ f) ≫ q = i ≫ p) : ((L.pull f w).pull i rfl).Isometric (L.pull (i ≫ f) h) :=
  have R := L.refines_pull_pull f w i rfl h
  HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy => ((R.φ σ c y hy).trans (add_zero _)).symm

theorem pol_vertical {D e : ℕ} (hB : IsArithVar q d) (hY : IsArithVar p D) (hD : e + (d + 1) = D) (f : Y ⟶ B) (w : f ≫ q = p)
    (L : Fin e → HermLB p) (A : Fin (d + 1) → HermLB q) {h : (Fin e ⊕ Fin (d + 1) → ℤ) → Y → ℝ}
    (hh : ∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).IsArithHeight (h n)) {Z : Scheme.{0}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] (hZ : topologicalKrullDim Z = D) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] : pol (fun n => h n (i (genericPoint Z))) = 0 := by
  have hp : IsProjOver (strHom (ZMod l) Z) := GlobalTheory.T.closed_subscheme_mod_l_projective k Y p D hY Z i l
  have h₁ := GlobalTheory.T.intersection_number_zero_small_image (ZMod l) e (d + 1) Z B hp (hD ▸ hZ.le) (i ≫ f)
    (dim_closure_lt hB (ne_genericPoint_of_vertical hB _ l _)) (fun a => (L a).B.pull i)
    (fun a => LB.isLB_pull (L a).isLB i) (fun a => (A a).B) fun a => (A a).isLB
  have h₂ : interNum (ZMod l) (structureModule Z)
      (fun a => ((Sum.elim L fun a => (A a).pull f w) a).B.pull i) = 0 := by
    refine (interNum_congr_lbIso _ _ (fun a => LB.isLB_pull (HermLB.isLB _) i) ?_ ?_).trans h₁
    · rintro (a | a)
      · exact LB.isLB_pull (L a).isLB i
      · exact LB.isLB_pull (A a).isLB _
    · rintro (a | a)
      · exact (CechPic.cls_eq_iff (LB.isLB_pull (L a).isLB i) (LB.isLB_pull (L a).isLB i)).1 rfl
      · exact ((A a).refines_pull_pull f w i rfl (by rw [Category.assoc, w])).lbIso
  simp only [fun n => (hh n).vertical Z i (ZMod l) D hZ]
  rw [pol_mul_const, GlobalTheory.T.polynomial_top_self_intersection k Y p (ZMod l) Z hp _ D (by simpa using hD) hZ.le i, h₂]
  simp

theorem arFun_prod (H : ArCalc) (hB : IsArithVar q d) (hs : GenSmooth q d) {A : Fin (d + 1) → HermLB q}
    {Φ : MvPolynomial (Fin (d + 1)) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) (e : ℕ) :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k), IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p)
      (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) →
      ∀ (L : Fin e → HermLB p) (Ψ : MvPolynomial (Fin e ⊕ Fin (d + 1)) ℝ →ₗ[ℝ] ℝ),
        IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → Ψ (∏ o, X o) =
          (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) *
            Φ (∏ a, X a) := by
  induction e with
  | zero =>
    intro Y _ p hY f w G j s h L Ψ hΨ
    have e := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY
      (isArFun_pull H hB hY f w h hΦ fun i => (L i).B.pull j) hΨ Sum.inr fun _ => rfl) (∏ a, X a)
    simpa [Fintype.prod_sum_type] using e.symm
  | succ e ih =>
    intro Y _ p hY f w G j s hG L Ψ hΨ
    have := hY.isNoetherian
    let N : Fin e ⊕ Fin (d + 1) → HermLB p := Sum.elim (fun a => L a.succ) fun a => (A a).pull f w
    have hc : Fintype.card (Fin e ⊕ Fin (d + 1)) = d + (e + 1) := by simp; omega
    obtain ⟨Φ', hΦ'⟩ := ((H.arExists k Y p _ hY).2 _ fun o : Option _ => o.elim (L 0) N).1
    choose h hh using fun n => (H.arExists k Y p _ hY).1 (comb N n)
    obtain ⟨r, hr⟩ := exists_isRatSec (L 0).isLB
    have hm := fun n => H.arMix k Y p _ hY _ (L 0) N Φ' hΦ' n (h n) (hh n) r hr
    have ha := GlobalTheory.T.arch_integrable_polynomial_vanishing k B Y q p d _ hs hY f w _ _ (by simp) (fun a : Fin e => L a.succ) A (L 0) r hr fun n => (hm n).1
    have key (z : Y) : ∃ c : ℤ, ((L 0).div hr).mult z ≠ 0 →
        pol (fun n => h n z) = (d + (e + 1)).factorial * (c * Φ (∏ a, X a)) ∧
        ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z)
          (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧
          IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧
          c = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G')
            (fun a : Fin e => ((L a.succ).B.pull i).pull j')) := by
      obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      have hP := IsPullback.of_hasPullback (i ≫ f) (B.fromSpecStalk (genericPoint B))
      refine ⟨_, fun hz => ⟨?_, Z, i, ‹_›, ‹_›, _, _, _, rfl, hP, rfl⟩⟩
      have hZ := GlobalTheory.T.codim_one_integral_subscheme_dim k Y p _ hY Z i (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
      rcases hY.vertical_or_horizontal i with ⟨l, _, ⟨_⟩⟩ | ⟨hc0, -⟩
      · rw [pol_vertical hB hY (by omega) f w _ A hh i hZ l, interNum_eq_zero_of_ne hP
          (ne_genericPoint_of_vertical hB _ l _) fun a : Fin e => LB.isLB_pull (LB.isLB_pull (L a.succ).isLB i) _]
        simp
      · have hZ' : IsArithVar (i ≫ p) (d + e) := hY.of_isClosedImmersion i hc0 hZ
        have w' : (i ≫ f) ≫ q = i ≫ p := by rw [Category.assoc, w]
        obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Z _ _ hZ').2 _ fun o => (N o).pull i rfl).1
        have e₁ (n) : h n (i (genericPoint Z)) = Ψ' (lin (fun o => (n o : ℝ)) ^ (d + (e + 1))) := by
          obtain ⟨t, ht, e₂⟩ := hΨ'.1 n
          exact ((hh n).isSelfInter_restrict hY i rfl).unique hZ'
            ⟨t, (H.arIso k Z _ _ hZ').1 _ _ t (isometric_comb_pull N n i rfl) ht, e₂⟩
        have hΨ'' := ((H.arIso k Z _ _ hZ').2 _ _ Ψ' hΨ').2.1
          (Sum.elim (fun a : Fin e => (L a.succ).pull i rfl) fun a => (A a).pull (i ≫ f) w') (by
            rintro (a | a)
            · exact .refl _
            · exact isometric_pull_pull _ f w i w')
        simp only [e₁]
        rw [pol_lin_pow Ψ' hc, ih Z _ hZ' _ w' _ _ _ hP _ Ψ' hΨ'']
        rfl
    choose γ hγ using key
    have hg := GlobalTheory.T.generic_fibre_intersection_formula k B Y q p d e hB hY f w G j s hG (fun a => (L a).B) (fun a => (L a).isLB) r hr γ
      fun z hz => (hγ z hz).2
    have hT := ((L 0).div hr).finite_support_mult
    have e₃ (u : Y → ℝ) : ∑ᶠ z, (((L 0).div hr).mult z : ℝ) * u z =
        ∑ z ∈ hT.toFinset, (((L 0).div hr).mult z : ℝ) * u z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₄ : ∑ᶠ z, ((L 0).div hr).mult z * γ z = ∑ z ∈ hT.toFinset, ((L 0).div hr).mult z * γ z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₅ := pol_mix Φ' hc
    simp only [fun n => (hm n).2, e₃] at e₅
    rw [pol_sub, ha, sub_zero, pol_sum, Finset.sum_congr rfl fun z hz => by
      rw [pol_const_mul, (hγ z (by simpa using hz)).1]] at e₅
    have e₆ := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY hΦ' hΨ
      (fun o => o.elim (.inl 0) (Sum.map Fin.succ id)) (by rintro (_ | a | a) <;> rfl)) (∏ o, X o)
    have e₇ : Φ' (∏ o, X o) = Ψ (∏ o, X o) := by
      simpa [Fintype.prod_option, Fintype.prod_sum_type, Fin.prod_univ_succ, mul_assoc] using e₆
    rw [hg, e₄, ← e₇]
    refine mul_left_cancel₀ (a := ((d + (e + 1)).factorial : ℝ)) (by positivity) (e₅.symm.trans ?_)
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring

theorem exists_monomial_eq_prod {κ : Type} (n : ℕ) (m : κ →₀ ℕ) (hm : m.degree = n) :
    ∃ r : Fin n → κ, (monomial m 1 : MvPolynomial κ ℝ) = ∏ a, X (r a) := by
  subst hm
  have hl : m.toMultiset.toList.length = m.degree := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  refine ⟨fun a => m.toMultiset.toList.get (a.cast hl.symm), ?_⟩
  refine Eq.trans ?_ ((finCongr hl.symm).prod_comp (fun a => (X (m.toMultiset.toList.get a) : MvPolynomial κ ℝ)) |>.trans
    (Fin.prod_univ_fun_getElem m.toMultiset.toList fun a => (X a : MvPolynomial κ ℝ))).symm
  rw [Multiset.prod_map_toList, ← prod_X_pow_eq_monomial, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
  rfl

open scoped Classical in

theorem arFun_mul_pull : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin e → HermLB p) (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin e ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous (d + 1) → Ψ ((∏ i : Fin e, MvPolynomial.X (Sum.inl i)) * rename Sum.inr P) = (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) * Φ P := by
  intro H k _ B Y _ _ q p d e hB hr hY f w G j s hG L κ _ A Φ Ψ hΦ hΨ P hP
  rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨r, e₀⟩ := exists_monomial_eq_prod (d + 1) m (by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.1 hm))
  obtain ⟨Φ', hΦ'⟩ := ((H.arExists k B q d hB).2 _ fun a => A (r a)).1
  obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Y p _ hY).2 _ (Sum.elim L fun a => (A (r a)).pull f w)).1
  have e₁ := arFun_prod H hB (RegGenSmooth.genSmooth hB hr) hΦ' e Y p hY f w G j s hG L Ψ' hΨ'
  rw [VertForm.FormEx.arFun_eq_rename H hB hΦ' hΦ r fun _ => rfl,
    VertForm.FormEx.arFun_eq_rename H hY hΨ' hΨ (Sum.map id r) (by rintro (a | a) <;> rfl)] at e₁
  rw [show monomial m (coeff m P) = coeff m P • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one], e₀, map_smul, mul_smul_comm, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, mul_left_comm]
  congr 1
  simpa [Fintype.prod_sum_type] using e₁

end GlobalTheory.FibreProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem exists_of_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : FractionRing O →+* ℂ) {N : ℕ}
    (hN : IsUnit (N : O)) {b : FractionRing O} {k : ℕ} (h : IsIntegral ℤ ((N : ℂ) ^ k * e b)) :
    ∃ o : O, algebraMap O (FractionRing O) o = b := by
  have h1 : IsIntegral O ((N : FractionRing O) ^ k * b) := by
    obtain ⟨f, hf, h0⟩ := h
    refine ⟨f.map (Int.castRingHom O), hf.map _, e.injective ?_⟩
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero, map_mul, map_pow, map_natCast, ← h0]
    congr 1
    exact RingHom.ext_int _ _
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨u, hu⟩ := hN.pow k
  refine ⟨(u⁻¹ : Oˣ) * y, ?_⟩
  have e2 : algebraMap O (FractionRing O) (u⁻¹ : Oˣ) * (N : FractionRing O) ^ k = 1 := by
    rw [← map_natCast (algebraMap O (FractionRing O)), ← map_pow, ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, hy, ← mul_assoc, e2, one_mul]

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem tmul_mem_realBase (hL : Links2 p) (h1 : KerOf p w j) (h2 : TraceOf p w j) (h3 : KerRat p w j) (h4 : LatIo p w j)
    (h5 : ReadCmp p w j) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    {rd : Can p w j} (hfit : Fit p w j hρ ν) (hcan : IsCan p rd) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j))
    {Q : PolF D (Wc D j).rank (Vc D j).rank} (hQ : Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h)
    {g : D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w)}
    (hg : rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q) :
    ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd := by
  classical
  have hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hguard : QGuard (R2 p) := p.qGuard
  obtain ⟨hpin, e, he1, he2⟩ := hfit.adapted
  obtain ⟨hν, c, hsc, n, hn, hνc⟩ := hfit.norm
  rw [p.phsOne j, map_one, one_mul] at hνc
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hνc
    exact hν ((pow_eq_zero_iff hn).1 hνc)
  obtain ⟨hBo, hQ', ξR, φ, hk⟩ := h1 ρ hρ hpin
  obtain ⟨u, hu, hio⟩ := h4 ρ hρ hpin c hc hsc
  obtain ⟨y, hy, hyio⟩ := hio h hh Q hQ
  have hU := hO D ex.nch w
  have hN0 : ownAt D (D.plEq w) ≠ 0 := fun h0 => by
    rw [h0, Nat.cast_zero] at hU
    exact not_isUnit_zero hU
  have hNC : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hpl : ∀ PP ∈ plW p w, ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => (Finset.mem_filter.1 hPP).2
  obtain ⟨z, cA, hz, hcA, hser⟩ := hF D _ _ _ _ _ (R2 p) (F2 p) hcore hguard j (p.pins j).2.lift.std _ (hρ.base _ j _) hBo _ ξR _ φ
    (by rw [hQ']; exact hk) ⟨_, by rw [hQ']; exact Finset.filter_subset _ _⟩ _ hN0 (by rw [hQ']; exact hpl)
  obtain ⟨m, hm⟩ := hC D _ _ _ _ _ (R2 p) j _ z hz _ hN0 (by rw [hQ']; exact hpl)
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hz.2.1
  have hy' := (hm h hh y).1 hy
  obtain ⟨x, hx⟩ := h3 _ _ _ _ hk (h * z) hhz _ hy' u hu
  obtain ⟨x', hx'⟩ := hTr D _ _ _ _ _ (R2 p) (F2 p) hcore hL.2.2.1 j (p.v₀ j _) ((fw2 p).hv₀ j _).1 _ _ _ _ _ _ hk
    (F2 p).P0 (F2 p).ψ0⁻¹ (h * z) _ u hu x hx
  have hmem : x' ∈ thetaBase (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) :=
    Submodule.subset_span ⟨_, φ, hk.isKernel, h * z, hhz, _, hy', fun v => by rw [one_smul]; exact hx' v⟩
  have hs0 : ∀ y', series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z)
      ((R2 p).ioP j (PiTensorProduct.tprod ℂ u) y') =
        singleSeries (R2 p) j (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z) y' u := fun y' => by
    funext g'
    rw [series_apply, hBo.fock_eq]
    rfl
  have hs := hs0 (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m • y)
  rw [map_smul, hyio, map_smul, map_smul, smul_smul] at hs
  have key : rdAt p w j hρ ν g = (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) • ν⁻¹ •
      adForm (R2 p) j x' (fun τ => u τ) := by
    rw [hg, h2 ρ hρ hpin hfit.level h Q, hser, map_smul, hx' u, ← hs, map_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  rcases h5 ρ hρ e he1 he2 ν hν rd hcan u hu g x' _ key with rfl | ⟨b, hb, hgb⟩
  · rw [TensorProduct.tmul_zero]
    exact zero_mem _
  · obtain ⟨-, k, hk1, -⟩ := hcA
    have hζ : IsIntegral ℤ (ν / c) := IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
      rw [div_pow, hνc, div_self (pow_ne_zero _ hc)]
      exact isIntegral_one)
    obtain ⟨o, ho⟩ := exists_of_integral e hU (b := b) (k := k + m) (by
      have e3 : ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (k + m) * (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
          (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ k * cA) * (ν / c) := by
        rw [pow_add]
        field_simp
      rw [hb, e3]
      exact hk1.mul hζ)
    rw [hgb, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x', hmem, rfl⟩)

theorem baseLat_le_realBase {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} {rd : Can p w j} (hfit : Fit p w j hρ ν)
    (hinj : Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hsm : ∀ h ∈ GfC (Vc D j), ∀ Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h, ∀ g,
      rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q →
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd) :
    baseLat p w j hρ ν ≤ realBase p rd := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ realBase p rd := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨g, hg⟩ := hfit.rat.1 s h Q ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      exact ⟨g, hg, hsm h hd.fin Q hQ g hg⟩
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add, e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen h P hd.mem)
  have e : f = g := hinj (hf.trans hg.symm)
  rw [e]
  exact hm

end Point

theorem baseGe_of_steps (hI : ReadInj) (hG : LatSmallGen) (h1 : KerOfAt) (h2 : TraceOfAt) (h3 : KerRatAt) (h4 : LatIoAt)
    (h5 : ReadCmpAt) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) : BaseGe := by
  unfold BaseGe AtFit ReadInj LatSmallGen KerOfAt TraceOfAt KerRatAt LatIoAt ReadCmpAt AtTw AtPts at *
  refine ((((((Formalism.MainNotions.Closed.and hI hG).and h1).and h2).and h3).and h4).and h5).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := H
  obtain ⟨x0, hx0⟩ := (((((a1.and a2).and a3).and a4).and a5).and a6).and a7
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hx0 x hx hle i p hp
  exact baseLat_le_realBase p w j hfit (b1 hm w hw j ρ hρ ν hfit.norm.1) (b2 hm w hw j ρ hρ hfit.pin) fun h hh Q hQ g hg =>
    tmul_mem_realBase p w j (GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hm.1) (b3 hm w hw j) (b4 hm w hw j) (b5 hm w hw j)
      (b6 hm w hw j) (b7 hm w hw j) hF hC hTr hO hfit hcan hh hQ hg

end GlobalTheory.BigOn.Exp.SerBase

namespace GlobalTheory.BigOn.Exp

theorem baseGe_of : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → BaseGe := fun hP hA hR hS =>
  SerBase.baseGe_of_steps GlobalTheory.T.ReadInjective GlobalTheory.T.LatticeSmallGeneration GlobalTheory.T.kernel_rationality_at_place GlobalTheory.T.trace_rationality_at_place (GlobalTheory.T.kernel_rationality_of_reciprocity hP hA hR hS) GlobalTheory.T.lattice_intersection_at_place GlobalTheory.T.lagrangian_set_additive_subgroup
    GlobalTheory.T.flatDatum_series_unit_times_kernel_series GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes GlobalTheory.T.ownPrime_isUnit_at_place

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetAbelianGaloisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_abelian_galois : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∀ i, (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 ≠ 0 ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0)
        (a i * (a i * ((Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2) / (D : ℂ)) * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ := by
  first | exact @GlobalTheory.CxPtSizes.scale_size | exact GlobalTheory.CxPtSizes.scale_size | (intros; apply GlobalTheory.CxPtSizes.scale_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLabStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  first | exact @GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero | exact GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero | (intros; apply GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero <;> assumption)
end

