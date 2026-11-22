import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSigns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockOpp

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem raiO_mul_lowO_apply {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (h : ∀ i j, ε' i ≠ ε j) (i : Fin b) (j k : Fin a) (P : PolF D b a) :
    (raiO τ ε ε' i j * lowO τ ε ε' i k) P =
      -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then P else 0) := by
  classical
  have hs : sgn (ε j) * sgn (ε k) = 1 := by
    have h1 := h i j
    have h2 := h i k
    unfold sgn
    cases hi : ε' i <;> cases hj : ε j <;> cases hk : ε k <;> simp_all
  unfold raiO lowO
  rw [if_neg (h i j), if_neg (h i k), smul_mul_smul_comm, hs, one_smul]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and]
  by_cases hjk : j = k
  · subst hjk
    simp only [if_true, mul_one]
    ring
  · simp [hjk, Ne.symm hjk]

theorem fockS_of_opposite {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin a) (Fin a) ℂ) (h : ∀ i j, ε' i ≠ ε j) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y =
      -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  classical
  refine LinearMap.ext fun P => ?_
  have key : ∀ (i : Fin b) (j k : Fin a),
      (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0 : Module.End ℂ (PolF D b a)) P =
        -(X (τ, i, k) * pderiv (τ, i, j) P) - (if j = k then (1 / 2 : ℂ) else 0) • P := by
    intro i j k
    rw [LinearMap.add_apply, raiO_mul_lowO_apply τ ε ε' h]
    by_cases hjk : j = k
    · simp only [hjk, if_true, LinearMap.smul_apply, Module.End.one_apply]
      module
    · simp [hjk]
  have htr : ∑ j, ∑ k, Y j k • ∑ _i : Fin b, (if j = k then (1 / 2 : ℂ) else 0) • P =
      (((b : ℂ) / 2) * Y.trace) • P := by
    simp only [← Finset.sum_smul, smul_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcol : (GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) P =
      ∑ j, ∑ k, Y j k • ∑ i : Fin b, (X (τ, i, k) * pderiv (τ, i, j) P : PolF D b a) := by
    rw [GlobalTheory.ColLie.colDer_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    rfl
  rw [LinearMap.sub_apply, LinearMap.neg_apply, hcol, LinearMap.smul_apply, Module.End.one_apply, ← htr]
  unfold fockS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    smul_sub, smul_neg]

end GlobalTheory.FockOpp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupAlgebraisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgGroupAdic

open GlobalTheory.AlgGroup (exists_point word_compat word_points)

variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {B : Over (Spec (CommRingCat.of R))}
  {b : ∀ e, (Y e).left ⟶ B.left}

theorem exists_hom [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R)
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProper Z.hom)
    (φ : ∀ e, thickObj R I e Z ⟶ Y e) (hφ : ∀ e, thickMap R I e Z ≫ (φ (e + 1)).left = (φ e).left ≫ β e) :
    ∃ g : Z ⟶ B, ∀ e, pullback.fst Z.hom (thick R I e) ≫ g.left = (φ e).left ≫ b e := by
  obtain ⟨g, hg, -⟩ := hM.existsUnique_thick hc₀ Z B (fun e => (φ e).left ≫ b e)
    (fun e => by
      rw [Category.assoc, (hb e).w, Over.w_assoc]
      exact pullback.condition.symm)
    (fun e => by rw [← Category.assoc, hφ, Category.assoc, hβb])
  exact ⟨g, hg⟩

theorem exists_word [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R) [∀ e, GrpObj (Y e)]
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left}
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    {κ : Type} (w : FreeGroup κ) (Z : Over (Spec (CommRingCat.of R))) (hZ : IsProper Z.hom)
    (p : κ → (Z ⟶ B)) :
    ∃ g : Z ⟶ B, ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z) (x : κ → (T ⟶ Y e)),
      (∀ i, (k ≫ p i).left = (x i).left ≫ b e) → (k ≫ g).left = (FreeGroup.lift x w).left ≫ b e := by
  have ex : ∀ e i, ∃ x : thickObj R I e Z ⟶ Y e,
      pullback.fst Z.hom (thick R I e) ≫ (p i).left = x.left ≫ b e := fun e i =>
    ⟨Over.homMk ((hb e).lift (pullback.fst Z.hom (thick R I e) ≫ (p i).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w, pullback.condition])) ((hb e).lift_snd _ _ _),
      ((hb e).lift_fst _ _ _).symm⟩
  choose X hX using ex
  obtain ⟨g, hg⟩ := exists_hom hM hc₀ hB hb hβb Z hZ (fun e => FreeGroup.lift (X e) w) fun e =>
    word_compat (hβ e) (hb (e + 1)) (hβb e) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))
      (pullback.lift_snd _ _ _) p (X e) (X (e + 1)) (hX e) (hX (e + 1)) w
  exact ⟨g, fun e T k x hx =>
    word_points (hb e) (IsPullback.of_hasPullback _ _) p (X e) (hX e) w g (hg e) T k x hx⟩

theorem hom_eq_of_points [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R)
    {Z : Over (Spec (CommRingCat.of R))} (hZ : IsProper Z.hom) [IsProper B.hom] {f g : Z ⟶ B}
    (h : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (k : Over.mk (T.hom ≫ thick R I e) ⟶ Z), (k ≫ f).left = (k ≫ g).left) : f = g := by
  refine hM.hom_ext hc₀ fun e ↦ ?_
  exact h e (thickObj R _ e Z) (Over.homMk (pullback.fst Z.hom (thick R _ e)) pullback.condition)

theorem exists_grpObj [IsNoetherianRing R] (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (hc₀ : IsAdicComplete I R) [∀ e, GrpObj (Y e)]
    (hc : ∀ e, IsCommMonObj (Y e)) (hB : IsProper B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B)
    (hm : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ Y e)
      (x₀ y₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e →
      (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e)
    (hi : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ Y e)
      (x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ B), x₀.left = x.left ≫ b e →
      (x₀ ≫ io).left = (x⁻¹).left ≫ b e)
    (hu : ∀ e (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ thick R I e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) :
    ∃ _ : GrpObj B, IsCommMonObj B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have ex := exists_point hb
  have h2 := isProper_tensorObj_over hB hB
  have h3 := isProper_tensorObj_over h2 hB
  have one_mul' : lift (toUnit B ≫ un) (𝟙 B) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T 1 x _ _ (hu e T) hx, _root_.one_mul, hx]
  have mul_one' : lift (𝟙 B) (toUnit B ≫ un) ≫ mu = 𝟙 B := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x 1 _ _ hx (hu e T), _root_.mul_one, hx]
  have linv : lift io (𝟙 B) ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T _ x _ _ (hi e T x k hx) hx, inv_mul_cancel, hu e T]
  have rinv : lift (𝟙 B) io ≫ mu = toUnit B ≫ un := by
    refine hom_eq_of_points hM hc₀ hB fun e T k ↦ ?_
    obtain ⟨x, hx⟩ := ex e T k
    rw [comp_lift_assoc, comp_toUnit_assoc, Category.comp_id,
      hm e T x _ _ _ hx (hi e T x k hx), mul_inv_cancel, hu e T]
  have assoc' : (mu ▷ B) ≫ mu = (α_ B B B).hom ≫ (B ◁ mu) ≫ mu := by
    refine hom_eq_of_points hM hc₀ h3 fun e T k ↦ ?_
    obtain ⟨p, q, r, rfl⟩ : ∃ p q r, k = lift (lift p q) r :=
      ⟨k ≫ fst _ _ ≫ fst _ _, k ≫ fst _ _ ≫ snd _ _, k ≫ snd _ _, by ext1 <;> [ext1; skip] <;> simp⟩
    obtain ⟨x, hx⟩ := ex e T p
    obtain ⟨y, hy⟩ := ex e T q
    obtain ⟨z, hz⟩ := ex e T r
    rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      hm e T _ z _ _ (hm e T x y _ _ hx hy) hz, hm e T x _ _ _ hx (hm e T y z _ _ hy hz),
      _root_.mul_assoc]
  let G : GrpObj B :=
    { one := un
      mul := mu
      inv := io
      one_mul := by
        rw [← cancel_epi (λ_ B).inv, Iso.inv_hom_id, ← one_mul', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ B).inv, Iso.inv_hom_id, ← mul_one', ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc'
      left_inv := linv
      right_inv := rinv }
  refine ⟨G, ⟨?_⟩, fun e ↦ ⟨hb e, fun T x y x₀ y₀ hx hy ↦ hm e T x y x₀ y₀ hx hy⟩⟩
  change (β_ B B).hom ≫ mu = mu
  refine hom_eq_of_points hM hc₀ h2 fun e T k ↦ ?_
  obtain ⟨p, q, rfl⟩ : ∃ p q, k = lift p q := ⟨k ≫ fst _ _, k ≫ snd _ _, by ext1 <;> simp⟩
  obtain ⟨x, hx⟩ := ex e T p
  obtain ⟨y, hy⟩ := ex e T q
  have := hc e
  rw [lift_braiding_hom_assoc, hm e T x y _ _ hx hy, hm e T y x _ _ hy hx, _root_.mul_comm]

theorem exists_grpObj_of_thickenings : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsCommMonObj (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProper B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  intro hM R _ _ I hc Y _ β hY hβ B b hB hb hβb
  obtain ⟨mu, hm⟩ := exists_word hM hc hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProper_tensorObj_over hB hB)
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hM hc hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hM hc hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (inferInstanceAs (IsProper (𝟙 _))) Empty.elim
  exact exists_grpObj hM hc hY hB hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)

end GlobalTheory.AlgGroupAdic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

def kerMat {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s t : Σ _ : Fin i, Fin i) : C :=
  if s.1 = t.1 then g t.2 s.2 else 0

def linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    MvPolynomial (Σ _ : Fin i, Fin i) C :=
  ∑ t, MvPolynomial.C (kerMat g s t) * MvPolynomial.X t

theorem isHomogeneous_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    (linP g s).IsHomogeneous 1 := by
  unfold linP
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun t _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem coe_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    ((linP g s : MvPolynomial (Σ _ : Fin i, Fin i) C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ t, kerMat g s t • (X t : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_X, smul_eq_C_mul]

theorem hasSubst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) :
    HasSubst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [coe_linP, map_sum]

theorem coeff_prod_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (d e : (Σ _ : Fin i, Fin i) →₀ ℕ)
    (h : e.degree ≠ d.degree) :
    coeff e (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) = 0 := by
  have hc : (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) =
      ((d.prod fun s n => linP g s ^ n : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, Finsupp.prod, Finsupp.prod, map_prod]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  rw [hc, MvPolynomial.coeff_coe]
  have hh : (d.prod fun s n => linP g s ^ n : MvPolynomial _ C).IsHomogeneous d.degree := by
    have := MvPolynomial.IsHomogeneous.prod d.support (fun s => linP g s ^ d s) (fun s => 1 * d s)
      fun s _ => (isHomogeneous_linP g s).pow _
    rw [Finsupp.prod]
    convert this using 1
    · simp only [one_mul]
      first | rfl | simp [Finsupp.degree_apply]
  exact hh.coeff_eq_zero h

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem derivAt0_eq_sum {σ : Type} (P : MvPolynomial σ C) (h : MvPowerSeries σ C) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) : derivAt0 P h = ∑ α ∈ S, P.coeff α * mfact α * coeff α h := by
  unfold derivAt0
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα]
  simp

theorem derivAt0_coe_eq_pair {σ : Type} (P Q : MvPolynomial σ C) :
    derivAt0 P (Q : MvPowerSeries σ C) = GlobalTheory.PolyPairingAdjoint.pair P Q := by
  simp only [derivAt0, GlobalTheory.PolyPairingAdjoint.pair, MvPolynomial.coeff_coe]
  rfl

theorem apply_le_degree {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  rw [Finsupp.degree_apply]
  by_cases hs : s ∈ α.support
  · exact Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) hs
  · rw [Finsupp.notMem_support_iff.1 hs]
    exact Nat.zero_le _

theorem le_const_of_degree_le {σ : Type} [Fintype σ] {α : σ →₀ ℕ} {N : ℕ} (h : α.degree ≤ N) :
    α ≤ Finsupp.equivFunOnFinite.symm (fun _ => N) := by
  intro s
  simpa using le_trans (apply_le_degree α s) h

theorem degree_le_totalDegree {σ : Type} {P : MvPolynomial σ C} {α : σ →₀ ℕ} (h : α ∈ P.support) :
    α.degree ≤ P.totalDegree := by
  have := MvPolynomial.le_totalDegree h
  rw [Finsupp.degree_apply]
  exact this

theorem derivAt0_subst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C)
    (P : MvPolynomial (Σ _ : Fin i, Fin i) C) (h : MvPowerSeries (Σ _ : Fin i, Fin i) C) :
    derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      derivAt0 (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P) h := by
  classical
  set P' := GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P
  set N := max P.totalDegree P'.totalDegree
  set n : (Σ _ : Fin i, Fin i) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => N)
  set Q := trunc' C n h
  have hL := hasSubst_linP g

  have h1 : ∀ e : (Σ _ : Fin i, Fin i) →₀ ℕ, e.degree ≤ N →
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C)) := by
    intro e he
    rw [coeff_subst hL, coeff_subst hL]
    refine finsum_congr fun d => ?_
    by_cases hd : e.degree = d.degree
    · rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos (le_const_of_degree_le (hd ▸ he))]
    · rw [coeff_prod_linP g d e hd, smul_zero, smul_zero]
  have h2 : subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C) =
      ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [subst_coe]
    have := congrArg (fun φ => φ Q) (MvPolynomial.comp_aeval (fun s => linP g s)
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := Σ _ : Fin i, Fin i) (R := C) C))
    simp only [AlgHom.comp_apply] at this
    rw [GlobalTheory.PolyPairingAdjoint.subst]
    exact this.symm
  calc derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h)
      = derivAt0 P ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
        rw [← h2]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [h1 α (le_trans (degree_le_totalDegree hα) (le_max_left _ _))]
    _ = GlobalTheory.PolyPairingAdjoint.pair P' Q := by
        rw [derivAt0_coe_eq_pair, GlobalTheory.PolyPairingAdjoint.pair_subst]
    _ = derivAt0 P' h := by
        rw [← derivAt0_coe_eq_pair]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [MvPolynomial.coeff_coe, coeff_trunc',
          if_pos (le_const_of_degree_le (le_trans (degree_le_totalDegree hα) (le_max_right _ _)))]

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem derivAt0_C_mul {σ : Type} (k : C) (P : MvPolynomial σ C) (h : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.C k * P) h = k * derivAt0 P h := by
  rw [derivAt0_eq_sum _ h P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul),
    derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_C_mul]
  ring

theorem subst_detPow {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (c : ℕ) :
    GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) (detPow C i c) =
      MvPolynomial.C (g.det ^ c) * detPow C i c := by
  classical
  have hM : (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s)).mapMatrix
      (Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C)) =
      (g.map MvPolynomial.C) * Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial _ C) := by
    ext a b
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.PolyPairingAdjoint.subst_X, Fintype.sum_sigma, kerMat]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  have hdet : (g.map MvPolynomial.C).det = (MvPolynomial.C g.det : MvPolynomial (Σ _ : Fin i, Fin i) C) :=
    (RingHom.map_det _ _).symm
  rw [detPow, map_pow, AlgHom.map_det, hM, Matrix.det_mul, hdet, mul_pow, map_pow]

theorem subst_linP_lin {i d : ℕ} (g : Matrix (Fin i) (Fin i) C) (u : Fin i → Fin d → C) (b : Fin i)
    (e : Fin d) :
    subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
    ∑ a, (fun a => ∑ a', g a a' • u a') a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  classical
  have inner : ∀ a : Fin i, (↑(linP g ⟨b, a⟩) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ a2, g a2 a • (X ⟨b, a2⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
    intro a
    rw [coe_linP, Fintype.sum_sigma, Finset.sum_eq_single b]
    · simp [kerMat]
    · intro b' _ hb'
      simp [kerMat, Ne.symm hb']
    · simp
  rw [← coe_substAlgHom (hasSubst_linP g), map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X (hasSubst_linP g), inner, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp [Finset.sum_apply, mul_comm]

theorem main : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 →
    detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  intro C _ _ v i d c G u g hg
  unfold detDepth depth
  have hE : expAlong (fun _ : Fin i => G) (fun _ => fun a => ∑ a', g a a' • u a') =
      fun x => subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
        (expAlong (fun _ : Fin i => G) (fun _ => u) x) := by
    funext x
    simp only [expAlong]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
      (GlobalTheory.DepthField.hasSubst_lin (fun _ : Fin i => u) x.1)) (hasSubst_linP g)]
    congr 1
    funext e
    exact (subst_linP_lin g u x.1 e).symm
  refine iInf_congr fun f => ?_
  rw [hE, ← subst_comp_subst_apply (GlobalTheory.DepthField.hasSubst_expAlong _ _) (hasSubst_linP g),
    derivAt0_subst_linP, subst_detPow, derivAt0_C_mul, v.map_mul, v.map_pow, hg, smul_zero, zero_add]

end

end GlobalTheory.DetDepthBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDifferentialOperatorDepthEqIInfMonomi
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthDegree

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth GlobalTheory.DepthField

variable {C : Type} [Field C]

theorem le_order_subst_monomial {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E)
    (h0 : ∀ s, constantCoeff (E s) = 0) (β : σ →₀ ℕ) :
    (((Finsupp.degree β : ℕ)) : ℕ∞) ≤ (subst E (monomial β (1 : C))).order := by
  classical
  rw [subst_monomial hE, map_one, one_mul, Finsupp.prod]
  refine le_trans ?_ (le_order_prod _ _)
  rw [show ((β.degree : ℕ) : ℕ∞) = ∑ s ∈ β.support, ((β s : ℕ) : ℕ∞) by
    rw [Finsupp.degree_apply, Nat.cast_sum]]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (h0 s)

theorem derivAt0_eq_zero_of_lt_order {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C)
    (h : (P.totalDegree : ℕ∞) < g.order) : derivAt0 P g = 0 := by
  refine Finset.sum_eq_zero fun α hα => ?_
  have h1 : (((Finsupp.degree α : ℕ)) : ℕ∞) < g.order := by
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast (MvPolynomial.le_totalDegree hα)
  rw [coeff_of_lt_order h1, mul_zero]

theorem depth_eq_iInf_monomial_degree_le : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), depth G u P = ⨅ β ∈ {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ P.totalDegree}, toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  intro C _ _ v κ _ _ d G ι _ _ u P
  rw [depth_eq_iInf_monomial]
  refine le_antisymm (le_iInf₂ fun β _ => iInf_le _ β) (le_iInf fun β => ?_)
  by_cases hβ : β.degree ≤ P.totalDegree
  · exact iInf₂_le β hβ
  · have h0 : ∀ x, constantCoeff (expAlong G u x) = 0 := fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
        ((isExp_expOf (G x.1)).1 x.2)
    have hz := derivAt0_eq_zero_of_lt_order P _ (lt_of_lt_of_le (by exact_mod_cast not_le.1 hβ)
      (le_order_subst_monomial (hasSubst_expAlong G u) h0 β))
    rw [hz, v.map_zero]
    exact le_top

end GlobalTheory.DepthDegree
end
end

