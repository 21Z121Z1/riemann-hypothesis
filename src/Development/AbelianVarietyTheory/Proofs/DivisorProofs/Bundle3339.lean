import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0618
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.ev_X {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k} (c : Chart G d)
    (n : ℕ) (i : Fin d) : c.ev n (X i) = c.x n i := by
  have hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n))) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i
  show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i
  rw [coe_substAlgHom, subst_X hs, constantCoeff_C]

theorem Chart.isMapOf_add : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k)
    (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k)
    (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ →
    c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  intro p k _ d e G H c c' ν f g φ ψ hν hf hg n j
  have hφ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' f).2 φ hf).1
  have hψ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' g).2 ψ hg).1
  let L : H.A n ⊗[k] H.A n →ₐ[k] G.A n := Algebra.TensorProduct.lift
    (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)
  have hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a) := fun a => by
    have h := congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))
    simp only [toPts_ofConv] at h
    exact h.trans (AlgHom.convMul_apply _ _ a)
  have hy : ∀ i, IsNilpotent (L (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map L
  have ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0 := fun i => by
    cases i with
    | inl i => exact hφ i
    | inr i => exact hψ i
  have hnil : ∀ t, IsNilpotent (c.ev n (X t)) := fun t => by
    rw [Chart.ev_X]; exact c.nil n t
  have h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i) := fun i => by
    cases i with
    | inl i =>
      change c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)
      rw [hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    | inr i =>
      change c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)
      rw [hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha
    (fun i => L (c'.x₂ n i)) hy h1 (ν j)
  have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n)
    (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)
  change c.ev n (subst (Sum.elim φ ψ) (ν j)) = _
  rw [e1, ← e2, hadd]
  exact congrArg L (hν n j)

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedClosedFibreProperCompleteLocalNoet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedFibreConn

open Classical in

theorem idem_eq_of_basicOpen {X : Scheme.{0}} {e e' : Γ(X, ⊤)} (he : e * e = e) (he' : e' * e' = e')
    (h : (X.basicOpen e : Set X) = X.basicOpen e') : e = e' := by
  have key : ∀ (a : Γ(X, ⊤)) (x : X) (hx : x ∈ (⊤ : X.Opens)), a * a = a →
      (X.presheaf.germ ⊤ x hx).hom a = if x ∈ X.basicOpen a then 1 else 0 := by
    intro a x hx ha
    have hg : (X.presheaf.germ ⊤ x hx).hom a * (X.presheaf.germ ⊤ x hx).hom a = (X.presheaf.germ ⊤ x hx).hom a := by
      rw [← map_mul, ha]
    split_ifs with hxa
    · have hu := (X.mem_basicOpen a x hx).1 hxa
      exact hu.mul_left_cancel (hg.trans (_root_.mul_one _).symm)
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((X.presheaf.germ ⊤ x hx).hom a) with h1 | h1
      · exact absurd ((X.mem_basicOpen a x hx).2 h1) hxa
      · have h0 : (X.presheaf.germ ⊤ x hx).hom a * (1 - (X.presheaf.germ ⊤ x hx).hom a) = 0 := by
          rw [mul_sub, _root_.mul_one, hg, sub_self]
        exact h1.mul_left_eq_zero.1 h0
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' fun x hx => ?_
  change (X.presheaf.germ ⊤ x hx).hom e = (X.presheaf.germ ⊤ x hx).hom e'
  rw [key e x hx he, key e' x hx he']
  have : (x ∈ X.basicOpen e) ↔ (x ∈ X.basicOpen e') := by
    change x ∈ (X.basicOpen e : Set X) ↔ x ∈ (X.basicOpen e' : Set X); rw [h]
  simp only [this]

theorem eq_zero_of_germ_closedFibre {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : X ⟶ Sp A)
    (hf : IsClosedMap f) (t : Γ(X, ⊤))
    (h : ∀ x, f x = closedPoint A → (X.presheaf.germ ⊤ x trivial).hom t = 0) : t = 0 := by
  let Z : Set X := {y | (X.presheaf.germ ⊤ y trivial).hom t = 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨W, hW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq X.presheaf y (show y ∈ (⊤ : X.Opens) from trivial) (show y ∈ (⊤ : X.Opens) from trivial) t 0
      (hy.trans (map_zero _).symm)
    refine ⟨W, fun y' hy' => ?_, W.isOpen, hW⟩
    have e₁ := TopCat.Presheaf.germ_res_apply X.presheaf iU y' hy' t
    have e₂ := TopCat.Presheaf.germ_res_apply X.presheaf iV y' hy' 0
    exact e₁.symm.trans ((congrArg _ e').trans (e₂.trans (map_zero _)))
  have hall : ∀ y, y ∈ Z := by
    by_contra hne
    obtain ⟨y, hy⟩ := not_forall.1 hne
    have hc : IsClosed (f '' Zᶜ) := hf _ hZ.isClosed_compl
    obtain ⟨y', hy', e⟩ := (IsLocalRing.specializes_closedPoint (R := A) (f y)).mem_closed hc ⟨y, hy, rfl⟩
    exact hy' (h y' e)
  exact TopCat.Presheaf.section_ext X.sheaf ⊤ t 0 fun y hy => (hall y).trans (map_zero _).symm

theorem thick_apply_eq (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ)
    (z : Spec (CommRingCat.of (A ⧸ maximalIdeal A ^ (e + 1)))) : thick A (maximalIdeal A) e z = closedPoint A := by
  apply PrimeSpectrum.ext
  show Ideal.comap _ _ = maximalIdeal A
  have := z.isPrime
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ z.asIdeal).ne_top) fun x hx => ?_
  show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom x ∈ z.asIdeal
  refine z.2.mem_of_pow_mem (e + 1) ?_
  rw [← map_pow, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx _)]
  exact z.asIdeal.zero_mem

theorem isPreconnected_closedFibre : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  intro A _ _ _ hA X f hf hX
  haveI := hf
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen]
  intro C hC
  let Y : Over (Sp A) := Over.mk f
  have hfst : ∀ e (y : (thickObj A (maximalIdeal A) e Y).left),
      f (pullback.fst Y.hom (thick A (maximalIdeal A) e) y) = closedPoint A := by
    intro e y
    rw [← Scheme.Hom.comp_apply]
    change (pullback.fst Y.hom (thick A (maximalIdeal A) e) ≫ Y.hom) y = _
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact thick_apply_eq A e _
  let D : ∀ e, Set (thickObj A (maximalIdeal A) e Y).left := fun e =>
    {y | (⟨pullback.fst Y.hom (thick A (maximalIdeal A) e) y, hfst e y⟩ : {x : X | f x = closedPoint A}) ∈ C}
  have hD : ∀ e, IsClopen (D e) := fun e =>
    hC.preimage ((pullback.fst Y.hom (thick A (maximalIdeal A) e)).continuous.subtype_mk (fun y => hfst e y))
  choose g hg hgD using fun e => GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ (D e) (hD e)
  have hcomp : ∀ e, thickMap A (maximalIdeal A) e Y ≫ pullback.fst Y.hom (thick A (maximalIdeal A) (e + 1)) =
      pullback.fst Y.hom (thick A (maximalIdeal A) e) := fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hcompat : ∀ e, (thickMap A (maximalIdeal A) e Y).appTop.hom (g (e + 1)) = g e := by
    intro e
    refine idem_eq_of_basicOpen (by rw [← map_mul, hg]) (hg e) ?_
    rw [← Scheme.preimage_basicOpen_top, hgD e]
    ext y
    change thickMap A (maximalIdeal A) e Y y ∈ ((thickObj A (maximalIdeal A) (e + 1) Y).left.basicOpen (g (e + 1)) : Set _) ↔ y ∈ D e
    rw [hgD (e + 1)]
    simp only [D, Set.mem_setOf_eq, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨s, hs⟩ := GlobalTheory.T.formalFunctions_exists_globalFunction_of_thickenings A (maximalIdeal A) hA Y hf g hcompat
  haveI : IsProper Y.hom := hf
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have ht : s * s - s = 0 := by
    refine eq_zero_of_germ_closedFibre f f.isClosedMap _ fun x hx => ?_
    refine GlobalTheory.FormalValue.germ_eq_zero_of_thickenings (maximalIdeal A) Y ⊤ (s * s - s) (fun e => ?_) x trivial ?_
    · change (pullback.fst Y.hom (thick A (maximalIdeal A) e)).appTop.hom (s * s - s) = 0
      rw [map_sub, map_mul, hs e, hg e, sub_self]
    · change maximalIdeal A ≤ (f x).asIdeal
      rw [hx]; exact le_rfl
  have hs2 : s * s = s := sub_eq_zero.1 ht
  have hB : IsClopen (X.basicOpen s : Set X) :=
    ⟨GlobalTheory.PairingLocus.isClosed_basicOpen (X := X) hs2, (X.basicOpen s).isOpen⟩
  have hne : (maximalIdeal A ^ (0 + 1)) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal A).ne_top
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨z₀⟩ : Nonempty (PrimeSpectrum (A ⧸ maximalIdeal A ^ (0 + 1))) := inferInstance
  have hC' : C = {c | c.1 ∈ (X.basicOpen s : Set X)} := by
    ext c
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.hom) (g := thick A (maximalIdeal A) 0)
      c.1 z₀ (c.2.trans (thick_apply_eq A 0 z₀).symm)
    have e1 : c ∈ C ↔ y ∈ D 0 := by
      change c ∈ C ↔ (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) ∈ C
      rw [show (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) = c from Subtype.ext hy]
    rw [e1, ← hgD 0, ← hs 0, ← Scheme.preimage_basicOpen_top]
    change pullback.fst Y.hom (thick A (maximalIdeal A) 0) y ∈ X.basicOpen s ↔ _
    rw [hy]; rfl
  rcases isClopen_iff.1 hB with h | h
  · left; rw [hC', h]; rfl
  · right; rw [hC', h]; rfl

end GlobalTheory.ClosedFibreConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegrees
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem resMap_bij12_of_fnMap {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (K : Cx C) (G : C' ⥤ C)
    (h : K.fnMap.PullbackBijectiveDegreesOneTwo) (h' : (K.res G).fnMap.PullbackBijectiveDegreesOneTwo) (h₀ : ((Cx.single K.M0).resMap G).PullbackBijectiveDegreesOneTwo) :
    (K.resMap G).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : (K.res G).fnMap.h1 ∘ (K.resMap G).h1 = ((Cx.single K.M0).resMap G).h1 ∘ K.fnMap.h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.1 _).1 (e ▸ h₀.1.comp h.1)
  · have e : (K.res G).fnMap.h2 ∘ (K.resMap G).h2 = ((Cx.single K.M0).resMap G).h2 ∘ K.fnMap.h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.2 _).1 (e ▸ h₀.2.comp h.2)

theorem resMap_comp_bij12 {C C' : Type 1} {C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    (K : Cx C) (G : C' ⥤ C) (H : C'' ⥤ C') (h : (K.resMap G).PullbackBijectiveDegreesOneTwo) (h' : ((K.res G).resMap H).PullbackBijectiveDegreesOneTwo) :
    (K.resMap (H ⋙ G)).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : ⇑(K.resMap (H ⋙ G)).h1 = ((K.res G).resMap H).h1 ∘ (K.resMap G).h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.1.comp h.1
  · have e : ⇑(K.resMap (H ⋙ G)).h2 = ((K.res G).resMap H).h2 ∘ (K.resMap G).h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.2.comp h.2

theorem Lift.resMap_toE_pullbackBijectiveDegreesOneTwo (D : Data) (Λ : Lift D) :
    (((KK D.κ D.t).res (pE D.κ D.t D.i)).resMap Λ.toE).PullbackBijectiveDegreesOneTwo := by
  obtain ⟨N₀, hN₀⟩ := (GlobalTheory.T.hom_spec_points_levels D Λ).2.2.2
  have mono : ∀ m n T, m ≤ n → LevE D.κ D.t D.i m T → LevE D.κ D.t D.i n T := fun m n T hmn hT ↦
    le_bot_iff.1 (((fil_properties _ _ T.obj.T.δ).2.2.1 m n hmn).trans (le_of_eq hT))
  have exh : ∀ T, ∃ n, LevE D.κ D.t D.i n T := fun T ↦ (isDPNilpotent_iff_exists_isLevel T.obj.T.δ).1 T.obj.T.nil
  have lev : ∀ N, N₀ + 1 ≤ N → ∃ h : ∀ U, LevE D.κ D.t D.i N (Λ.toE.obj U),
      ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i N).ι).resMap
        ((LevE D.κ D.t D.i N).lift Λ.toE h)).Bij := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact ⟨fun U ↦ hN₀ _ (by omega) U, GlobalTheory.T.crystallineForms_restriction_affineLift_bijective D Λ n _⟩
  exact ⟨GlobalTheory.T.h1_resMap_bijective_of_exhausting_properties _ _ _ _ Λ.toE (N₀ + 1) mono exh lev, GlobalTheory.T.bijective_restriction_fourTermComplex_of_exhaustion _ _ _ _ Λ.toE (N₀ + 1) mono exh lev⟩

theorem Lift.resMap_lift_pullbackBijectiveDegreesOneTwo : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  intro D Λ
  have hp := GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ _ D.t _ D.i
  have hg := GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter D.R D.I D.κ _ D.t _ D.i D.smooth_mono_inf.2.2
  exact resMap_comp_bij12 (KK D.κ D.t) (pE D.κ D.t D.i) Λ.toE
    (resMap_bij12_of_fnMap _ _ hp.1 hp.2 hg) (Lift.resMap_toE_pullbackBijectiveDegreesOneTwo D Λ)

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)

include hI hR hq hd hT in

theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl

include hI hR hq hd hT in

theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesUnitEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage1

theorem stage1 : Hypotheses3 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PGUnit F ∧ R.PGEquiv F ∧ (R.toCx3 F).zs.InBlock ∧ R.PThmA ∧ R.PThmB := by
  intro P D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  obtain ⟨_hGiven, _hGS, _hCD, hLI, hTR, _hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod P.q9
  have hOk := GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed R F hT.char hT.junk
  have hGU : R.PGUnit F := GlobalTheory.gUnit_of_models R F hT.char.base.models
  have hGE : R.PGEquiv F := GlobalTheory.GEquivCx.pGEquiv_of_baseW P.q2 R F hT.char.base hT.ex
  have hBlk : (R.toCx3 F).zs.InBlock := GlobalTheory.Hk3.inBlock_of_cuspRapidDecay P.q2 R F hLI hT.ok hT.char hT.ex hGE
  have hA : R.PThmA := GlobalTheory.T.thetaLift_theoremA_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hJ
  have hB : R.PThmB := GlobalTheory.T.thetaLift_theoremB_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ
  exact ⟨hOk, hGU, hGE, hBlk, hA, hB⟩

end GlobalTheory.Stage1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRatioRealizationSame
section
set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

namespace GlobalTheory.BigOn.Exp

theorem seriesUnit : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → AtTw fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  intro h1 h2 h3 h4
  have hI := readInj
  have hS := GlobalTheory.T.scaleRoot_of_cuspRapidDecay_of_reciprocity_of_rayClassField h1 h2 h3 h4
  have hC := GlobalTheory.T.norm_ratio_realization_same_dual h1 h2 h3 h4
  have hR := coordRange
  unfold ReadInj at hI
  unfold ScaleRoot at hS
  unfold CoordRange at hR
  unfold AtTw AtPts at hI hS hC hR ⊢
  refine Closed.imp (Closed.and (Closed.and (Closed.and hI hS) hC) hR) ?_
  intro eps Fm CH _ h
  obtain ⟨x0, hx0⟩ := EvPt.and (EvPt.and (EvPt.and h.1.1.1 h.1.1.2) h.1.2) h.2
  refine ⟨x0, ?_⟩
  intro x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f f' hf hf'
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hx0 x hx hle i p hp
  have hν : ν ≠ 0 := hN.1
  have hν' : ν' ≠ 0 := hN'.1
  have inj' := a1 hm w hw j ρ' hρ' ν hν
  have inj := a1 hm w hw j ρ hρ ν hν
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : rdAt p w j hρ' ν' f' = rdAt p w j hρ' ν' 0 := by
      rw [hf', ← hf, map_zero, map_zero]
    have := a1 hm w hw j ρ' hρ' ν' hν' h0
    exact ⟨1, ⟨1, one_ne_zero, one_pow 1⟩, by rw [this, smul_zero]⟩
  · have hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 := by
      intro h0
      apply hf0
      apply inj
      rw [hf, h0, map_zero]
    obtain ⟨n, hn, hnn⟩ := a2 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hpin' hSB hN hN' hR0 hR0' s h P hd hP hθ
    obtain ⟨c, ⟨m, hm0, hcm⟩, hc⟩ := a3 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hcm
      exact zero_ne_one hcm
    have hap := fun ν₁ g =>
      realRd_apply p.nexp p.v₀ hρ' ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν₁ g
    have key : rdAt p w j hρ' ν f' = (ν' * ν⁻¹ * c⁻¹) • rdAt p w j hρ' ν f := by
      rw [hc, ← hf', smul_smul]
      have e1 := hap ν f'
      have e2 := hap ν' f'
      simp only [rdAt]
      rw [e1, e2, smul_smul]
      congr 1
      field_simp
    obtain ⟨u, hu⟩ := a4 hm w hw j ρ' hρ' ν _ hν f f' hf0 key
    refine ⟨u, ⟨n * m, mul_ne_zero hn hm0, ?_⟩, ?_⟩
    · apply (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).injective
      rw [map_pow, map_one, hu, mul_pow, mul_pow, pow_mul ν', hnn, ← pow_mul, inv_pow, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ hν), mul_comm n m, pow_mul c, hcm]
      simp
    · apply inj'
      rw [key, map_smulₛₗ, hu]

end GlobalTheory.BigOn.Exp
end

