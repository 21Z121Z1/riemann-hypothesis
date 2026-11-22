import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankLeOfWeightsUnipotentSymplectic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.InvExt

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = ι[G'] := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁] at e
  refine e.trans ?_
  show (𝟙 G'.left ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).mpr (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]; exact bot_le)

theorem exists_common {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (u : Sp k ⟶ X)
    (u' : Sp k' ⟶ X) (x : Sp k) (x' : Sp k') (h : u x = u' x') :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp k) (v' : Sp K ⟶ Sp k'),
      v ≫ u = v' ≫ u' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' h
  let F := (pullback u u').residueField z
  let w : Sp (AlgebraicClosure F) ⟶ pullback u u' :=
    spMap (algebraMap F (AlgebraicClosure F)) ≫ (pullback u u').fromSpecResidueField z
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, w ≫ pullback.fst _ _,
    w ≫ pullback.snd _ _, by simp [pullback.condition]⟩

variable (C : Core)

theorem isOpenImmersion_a : IsOpenImmersion C.a := by
  have : IsOpenImmersion (C.a ≫ C.G.ι) := MorphismProperty.of_isPullback C.cart.flip inferInstance
  exact IsOpenImmersion.of_comp C.a C.G.ι

variable {C}

theorem generic_inv {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j) (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left)
    (ha : a₀ ≫ C.a = gPt p ≫ c ≫ τ.f) :
    gPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = a₀ ≫ (ι[C.A]).left ≫ C.a := by
  have := isOpenImmersion_a C
  have hinj : Function.Injective ((OO p).subtype.comp τ.j) := Subtype.val_injective.comp τ.j_inj
  let k : FractionRing τ.V →+* PadicAlgCl p := IsFractionRing.lift hinj
  have hk : spMap k ≫ Out.jK τ.V = gPt p ≫ spMap τ.j := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [k]
  let l : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V) :=
    pullback.lift (gPt p ≫ c) (spMap k) (by rw [Category.assoc, hc, hk])
  have hl : l ≫ pullback.fst _ _ = gPt p ≫ c := pullback.lift_fst _ _ _
  have h1 : l ≫ τ.φ = a₀ := by
    rw [← cancel_mono C.a, Category.assoc, τ.φ_f, reassoc_of% hl, ha]
  have h2 := inv_left_comp τ.φ_cart
  have h3 := inv_left_comp (isGrpPullback_pullback τ.H (Out.jK τ.V))
  have h4 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ τ.φ ≫ C.a =
      τ.φ ≫ (ι[C.A]).left ≫ C.a := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ C.a) h2
  have h5 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ pullback.fst τ.H.hom (Out.jK τ.V) ≫ τ.f =
      pullback.fst τ.H.hom (Out.jK τ.V) ≫ (ι[τ.H]).left ≫ τ.f := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ τ.f) h3
  rw [← h1, Category.assoc, ← h4, τ.φ_f]
  erw [h5]
  rw [reassoc_of% hl]

theorem range_residue {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    {K : Type} [Field K] (v : Sp K ⟶ Sp (kb p)) :
    Set.range (v ≫ rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
  have := τ.j_loc
  have h : ∀ x : Sp K, (v ≫ rPt p ≫ spMap τ.j) x = IsLocalRing.closedPoint τ.V := by
    intro x
    have hx : v x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
    exact (congrArg (spMap τ.j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint τ.j)
  ext x
  exact ⟨fun ⟨z, hz⟩ => hz ▸ h z, fun hx => ⟨IsLocalRing.closedPoint K, (h _).trans hx.symm⟩⟩

theorem rPt_apply (p : ℕ) [Fact p.Prime] (x : Sp (kb p)) : rPt p x = cPt p := by
  have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  rw [hx]
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))

theorem exists_common_residue {X : Scheme.{0}} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp (kb p)) (v' : Sp K ⟶ Sp (kb q)),
      v ≫ rPt p ≫ α = v' ≫ rPt q ≫ β := by
  obtain ⟨x⟩ : Nonempty (Sp (kb p)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Sp (kb q)) := inferInstance
  refine exists_common _ _ x x' ?_
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, rPt_apply, rPt_apply, h]

theorem natCast_kb (p : ℕ) [hp : Fact p.Prime] : (p : kb p) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (OO p)), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change Valued.v (p : PadicAlgCl p) < 1
  rw [PadicAlgCl.valuation_p, one_div]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem prime_eq {X : Scheme.{0}} {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) : p = q := by
  obtain ⟨K, _, _, v, v', -⟩ := exists_common_residue α β h
  have h1 : (p : K) = 0 := by
    rw [← map_natCast (Spec.preimage v).hom]
    exact (congrArg _ (natCast_kb p)).trans (map_zero _)
  have h2 : (q : K) = 0 := by
    rw [← map_natCast (Spec.preimage v').hom]
    exact (congrArg _ (natCast_kb q)).trans (map_zero _)
  have := (CharP.charP_iff_prime_eq_zero hp.out).mpr h1
  have := (CharP.charP_iff_prime_eq_zero hq.out).mpr h2
  exact CharP.eq K ‹CharP K p› ‹CharP K q›

theorem special_inv (hF : C.FibLaw) {p : ℕ} [Fact p.Prime] {y y' : Sp (OO p) ⟶ C.Z}
    (τ : C.Test y) (τ' : C.Test y')
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j)
    (c' : Sp (OO p) ⟶ τ'.H.left) (hc' : c' ≫ τ'.H.hom = spMap τ'.j)
    (h : (c ≫ τ.f) (cPt p) = (c' ≫ τ'.f) (cPt p)) :
    (c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p) = (c' ≫ (ι[τ'.H]).left ≫ τ'.f) (cPt p) := by
  obtain ⟨K, _, _, v, v', hv⟩ := exists_common_residue _ _ h
  let d : Over.mk (v ≫ rPt p ≫ spMap τ.j) ⟶ τ.H := Over.homMk (v ≫ rPt p ≫ c) (by simp [hc])
  let d' : Over.mk (v' ≫ rPt p ≫ spMap τ'.j) ⟶ τ'.H := Over.homMk (v' ≫ rPt p ≫ c') (by simp [hc'])
  have hd : d.left ≫ τ.f = d'.left ≫ τ'.f := by simpa [d, d'] using hv
  have hr : (v ≫ rPt p ≫ spMap τ.j) ≫ τ.y₀ = (v' ≫ rPt p ≫ spMap τ'.j) ≫ τ'.y₀ := by
    have := congrArg (· ≫ C.GG.hom) hv
    simp only [Category.assoc, τ.f_over, τ'.f_over, reassoc_of% hc, reassoc_of% hc'] at this
    simpa using this
  have e := (hF p y y' τ τ' K _ _ (range_residue τ v) (range_residue τ' v') hr d d d' d' hd hd).2
  have e' : v ≫ rPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = v' ≫ rPt p ≫ c' ≫ (ι[τ'.H]).left ≫ τ'.f := by
    simpa [Hom.inv_def, d, d'] using e
  obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
  have := congrArg (fun g => g x) e'
  simp only [Scheme.Hom.comp_apply, rPt_apply] at this
  simpa only [Scheme.Hom.comp_apply] using this

theorem exists_test (hT : C.HasTests) {p : ℕ} [Fact p.Prime] (α : Sp (OO p) ⟶ C.G.toScheme)
    (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left) (b : Sp (OO p) ⟶ C.P.left) (ha : a₀ ≫ C.a = gPt p ≫ α)
    (hb : gPt p ≫ b = a₀ ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = α ≫ C.GG.hom) :
    ∃ (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left),
      c ≫ τ.H.hom = spMap τ.j ∧ c ≫ τ.f = α ∧ b = (c ≫ (ι[τ.H]).left ≫ τ.f) ≫ C.G.ι := by
  have hw : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by simpa using C.cart.w
  have hcl : C.Cl (α ≫ C.GG.hom) := by
    rintro _ ⟨x, rfl⟩
    rw [← reassoc_of% ha, hw, ← Category.assoc, Scheme.Hom.comp_apply]
    exact Subtype.property _
  obtain ⟨τ⟩ := hT p _ hcl
  obtain ⟨c, hc, hcf⟩ := τ.lift α rfl
  refine ⟨_, τ, c, hc, hcf, ?_⟩
  have := C.proper
  have := isDominant_gPt p
  refine ext_of_isDominant_of_isSeparated C.P.hom ?_ (gPt p) ?_
  · have h1 : τ.f ≫ C.G.ι ≫ C.P.hom = τ.H.hom ≫ τ.y₀ := τ.f_over
    simp only [Category.assoc]
    rw [hb', h1, Over.w_assoc, reassoc_of% hc, τ.fac]
  · rw [hb, ← Category.assoc (gPt p), generic_inv τ c hc a₀ (by rw [hcf, ha])]
    simp only [Category.assoc]

end GlobalTheory.InvExt

namespace GlobalTheory

open InvExt in

theorem exists_inv_extension : ∀ C : Core, C.HasTests → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → C.FibLaw → ∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a := by
  intro C hT hS _ hF
  have := isOpenImmersion_a C
  have := C.flat
  have := C.lft
  have := C.qc
  have := C.proper
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian (C.P.hom ≫ C.π)
  have : QuasiCompact C.GG.hom := inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom))
  obtain ⟨z, hz⟩ := C.ne
  have : Nonempty C.G.toScheme := ⟨C.e z⟩
  have hI : IsIntegral C.G.toScheme := isIntegral_of_isOpenImmersion C.G.ι
  have hw : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by simpa using C.cart.w
  let e := C.a.isoOpensRange
  have he : e.inv ≫ C.a = C.a.opensRange.ι := C.a.isoOpensRange_inv_comp
  have he' : e.hom ≫ C.a.opensRange.ι = C.a := C.a.isoOpensRange_hom_ι
  obtain ⟨Φ, ⟨h1, h2⟩, -⟩ := @existsUnique_extension_of_finite_specializations C.G.toScheme hI
    (C.GG.hom ≫ C.π) inferInstance inferInstance inferInstance
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal)
    C.Z C.P.left C.GG.hom C.P.hom _ C.G C.a.opensRange
    (e.inv ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) ⟨_, eSec C.A (⟨z, hz⟩ : C.U), rfl⟩
    (by
      have h : C.a ≫ C.G.ι ≫ C.P.hom = C.A.hom ≫ C.U.ι := hw
      simp only [Category.assoc]
      rw [h, Over.w_assoc, ← hw, reassoc_of% he])
    (by
      intro σ _
      let F : Set C.P.left := {w | ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ C.Z)
        (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left), c ≫ τ.H.hom = spMap τ.j ∧
          (c ≫ τ.f) (cPt p) = σ ∧ w = C.G.ι ((c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p))}
      refine ⟨F, Set.Subsingleton.finite ?_, ?_, ?_⟩
      · rintro _ ⟨p, _, y, τ, c, hc, hσ, rfl⟩ _ ⟨q, _, y', τ', c', hc', hσ', rfl⟩
        obtain rfl := prime_eq _ _ (hσ.trans hσ'.symm)
        rw [special_inv hF τ τ' c hc c' hc' (hσ.trans hσ'.symm)]
      · rintro _ ⟨p, _, y, τ, c, hc, hσ, rfl⟩
        exact Subtype.property _
      · intro p _ α a₀ b hσ ha hb hb'
        obtain ⟨y, τ, c, hc, hcf, rfl⟩ := exists_test hT α (a₀ ≫ e.inv) b
          (by rw [Category.assoc, he, ha]) (by rw [hb, Category.assoc]) hb'
        exact ⟨p, _, y, τ, c, hc, hcf ▸ hσ, Scheme.Hom.comp_apply _ _ _⟩)
  refine ⟨Over.homMk Φ h2, ?_⟩
  rw [← cancel_mono C.G.ι]
  change (C.a ≫ Φ) ≫ C.G.ι = _
  rw [Category.assoc, Category.assoc]
  conv_lhs => rw [← he', Category.assoc, h1, e.hom_inv_id_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcs
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma weight_fin_two (m n : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) e = m * e 0 + n * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma leading_polynomial_eq_zero_iff_lt_weightedOrder {k : Type} [Field k] {m n : ℕ} (hm : 1 ≤ m)
    (f : MvPowerSeries (Fin 2) k) {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)) = 0 ↔
      (D : ℕ∞) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f := by
  have hcoeff : ∀ e ∈ S,
      (∑ e' ∈ S, Polynomial.C (MvPowerSeries.coeff e' f) * Polynomial.X ^ (e' 1)).coeff (e 1) =
        MvPowerSeries.coeff e f := by
    intro e he
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single e]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro e' he' hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h1
      apply hne
      have w1 := (hS e').1 he'
      have w2 := (hS e).1 he
      rw [weight_fin_two] at w1 w2
      rw [h1] at w2
      have h0 : e' 0 = e 0 :=
        Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (w1.trans w2.symm))
      ext i
      fin_cases i
      · exact h0
      · exact h1.symm
    · intro h; exact absurd he h
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have heq : MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f = D := le_antisymm hlt hD
    obtain ⟨e, hne, hwe⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder
      (![m, n] : Fin 2 → ℕ) (f := f) (by rw [heq]; rfl)
    rw [heq, Nat.cast_inj] at hwe
    have := hcoeff e ((hS e).2 hwe)
    rw [h0, Polynomial.coeff_zero] at this
    exact hne this.symm
  · intro hlt
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (by rw [(hS e).1 he]; exact hlt),
      map_zero, zero_mul]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma prod_pow_fin_two {k : Type} [Field k] (z w : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    (e.prod fun s j => (![z, w] : Fin 2 → PowerSeries k) s ^ j) = z ^ e 0 * w ^ e 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open PowerSeries in
private lemma coeff_pow_mul_pow_of_le_order {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order) (a b : ℕ) :
    (∀ j < m * a + n * b, coeff j (z ^ a * w ^ b) = 0) ∧
      coeff (m * a + n * b) (z ^ a * w ^ b) = coeff m z ^ a * coeff n w ^ b := by
  obtain ⟨z', rfl⟩ : X ^ m ∣ z := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hz)
  obtain ⟨w', rfl⟩ : X ^ n ∣ w := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hw)
  have hprod : (X ^ m * z') ^ a * (X ^ n * w') ^ b = X ^ (m * a + n * b) * (z' ^ a * w' ^ b) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  rw [hprod]
  refine ⟨fun j hj => by rw [coeff_X_pow_mul', if_neg (by omega)], ?_⟩
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow,
    map_pow]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_zero_of_lt {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {f : MvPowerSeries (Fin 2) k}
    {D : ℕ} (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f) {j : ℕ}
    (hj : j < D) : PowerSeries.coeff j (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) = 0 := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases hlt : Finsupp.weight (![m, n] : Fin 2 → ℕ) e < D
  · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
      (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
  · rw [weight_fin_two] at hlt
    rw [prod_pow_fin_two, ← PowerSeries.coeff,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 j (by omega), smul_zero]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_pow_mul_eval_leading {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {s t : k}
    (hzs : PowerSeries.coeff m z = s ^ m) (hwt : PowerSeries.coeff n w = s ^ n * t)
    {f : MvPowerSeries (Fin 2) k} {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    PowerSeries.coeff D (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) =
      s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := S)]
  · rw [Polynomial.eval_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hwe := (hS e).1 he
    rw [weight_fin_two] at hwe
    rw [prod_pow_fin_two, ← PowerSeries.coeff, ← hwe,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).2, hzs, hwt]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [pow_add, pow_mul, pow_mul]
    ring
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.mem_coe, hS]
    by_contra hne
    apply he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
        (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
    · rw [weight_fin_two] at hgt
      rw [prod_pow_fin_two, ← PowerSeries.coeff,
        (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 D (by omega), smul_zero]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.exists_polynomial_leading_quotient_subst :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  intro k _ _ m n hm hn r h d hd hdh
  have hfin : ((MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat : ℕ∞) =
      MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d :=
    ENat.coe_toNat ((MvPowerSeries.weightedOrder_eq_top_iff _).not.2 hd)
  set D := (MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat with hD_def
  have hWpos : ∀ x, (![m, n] : Fin 2 → ℕ) x ≠ 0 := by
    intro x; fin_cases x <;> simp <;> omega
  set S := (Finsupp.finite_of_nat_weight_le _ hWpos D).toFinset.filter
    fun e => Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D with hS_def
  have hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D := by
    intro e
    simp only [hS_def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hDd : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d := hfin.le
  have hDh : ∀ i, (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) :=
    fun i => hfin.le.trans (hdh i)
  refine ⟨∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e d) * Polynomial.X ^ (e 1),
    fun i => ∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e (h i)) * Polynomial.X ^ (e 1), ?_, ?_, ?_⟩
  · intro h0
    have := (leading_polynomial_eq_zero_iff_lt_weightedOrder hm d hDd S hS).1 h0
    rw [hfin] at this
    exact lt_irrefl _ this
  · intro i
    rw [leading_polynomial_eq_zero_iff_lt_weightedOrder hm (h i) (hDh i) S hS, hfin]
  · intro s t z w hs0 hz hw hzs hwt hPd
    have hz0 : PowerSeries.coeff 0 z = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)
    have hw0 : PowerSeries.coeff 0 w = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hn) hw)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hz0 hw0
    have hsub : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i
        · exact hz0
        · exact hw0
    have factor : ∀ f : MvPowerSeries (Fin 2) k,
        (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f →
        ∃ g : PowerSeries k, MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f =
          PowerSeries.X ^ D * g ∧ PowerSeries.constantCoeff g =
            s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
      intro f hf
      obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.2 fun j hj =>
        coeff_subst_eq_zero_of_lt hz hw hsub hf hj
      refine ⟨g, hg, ?_⟩
      have := coeff_subst_eq_pow_mul_eval_leading hz hw hsub hzs hwt hf S hS
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] at this
      exact this
    obtain ⟨gd, hgd, hgd0⟩ := factor d hDd
    have hgd0' : PowerSeries.constantCoeff gd ≠ 0 := by
      rw [hgd0]; exact mul_ne_zero (pow_ne_zero _ hs0) hPd
    refine ⟨?_, fun i => (factor (h i) (hDh i)).choose * gd⁻¹, fun i => ?_⟩
    · rw [hgd]
      exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
        fun h0 => hgd0' (by rw [h0, map_zero])
    · obtain ⟨hgi, hgi0⟩ := (factor (h i) (hDh i)).choose_spec
      constructor
      · rw [hgd, hgi, show (factor (h i) (hDh i)).choose * gd⁻¹ * (PowerSeries.X ^ D * gd) =
          PowerSeries.X ^ D * (factor (h i) (hDh i)).choose * (gd * gd⁻¹) by ring,
          PowerSeries.mul_inv_cancel _ hgd0', _root_.mul_one]
      · rw [map_mul, PowerSeries.constantCoeff_inv, hgi0, hgd0]
        field_simp

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrderStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_modelHasJacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  first | exact @GlobalTheory.SS.Ord.existsUnique_hasOrd | exact GlobalTheory.SS.Ord.existsUnique_hasOrd | (intros; apply GlobalTheory.SS.Ord.existsUnique_hasOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankLeOfWeightsUnipotentSymplecticStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic : ∀ (𝕜 V : Type) [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V), B.Nondegenerate → (∀ x y, B y x = - B x y) → ∀ (S Φ : V ≃ₗ[𝕜] V) (q : ℕ), 2 ≤ q → IsNilpotent ((S : V →ₗ[𝕜] V) - 1) → (∀ x y, B (S x) (S y) = B x y) → (∀ x y, B (Φ x) (Φ y) = q * B x y) → Φ * S = S ^ q * Φ → ∀ (W : Submodule 𝕜 V) (P : Polynomial ℤ), (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ x ∈ W, Φ x = (q : 𝕜) • x) → (∀ x, S x = x → Polynomial.aeval (Φ : V →ₗ[𝕜] V) P x ∈ W) → Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker ((S : V →ₗ[𝕜] V) - 1)) + Module.finrank 𝕜 W := by
  first | exact @GlobalTheory.SS.LinCore.finrank_le_of_weights | exact GlobalTheory.SS.LinCore.finrank_le_of_weights | (intros; apply GlobalTheory.SS.LinCore.finrank_le_of_weights <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericIsomorphismProductModelsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isomorphism_product_models : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  first | exact @GlobalTheory.SS.GenProj.genIso_of_prod | exact GlobalTheory.SS.GenProj.genIso_of_prod | (intros; apply GlobalTheory.SS.GenProj.genIso_of_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfinitePowCharEqOneOfAdditiveFamilyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_pth_roots_of_additive_family : ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k) (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) → Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 → em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  first | exact @GlobalTheory.infinite_pow_char_eq_one_of_additive_family | exact GlobalTheory.infinite_pow_char_eq_one_of_additive_family | (intros; apply GlobalTheory.infinite_pow_char_eq_one_of_additive_family <;> assumption)
end

