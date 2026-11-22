import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3602
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3664
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3514
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3667
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelOfPrincipalisation
section
namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantRatioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_constant_ratio : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  first | exact @GlobalTheory.ConstRatio.bottomTri_factor | exact GlobalTheory.ConstRatio.bottomTri_factor | (intros; apply GlobalTheory.ConstRatio.bottomTri_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.canon_pull_unif | exact GlobalTheory.Mum.canon_pull_unif | (intros; apply GlobalTheory.Mum.canon_pull_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinementsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_mumford_family_uniformises_refinements : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.CanonFam.exists_unif_refines | exact GlobalTheory.Mum.CanonFam.exists_unif_refines | (intros; apply GlobalTheory.Mum.CanonFam.exists_unif_refines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByPrimeAtEtalePlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.GeoCard

theorem card_ker_elt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {w0 : Ideal (𝓞 D.F)} (hw : IsEtPlace b w0) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) :
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (p + ringChar k + 1)
  have hℓp : ℓ ≠ p := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k (ringChar k)]
    intro hd
    rcases (Nat.dvd_prime hℓ).1 hd with h1 | h1
    · exact CharP.ringChar_ne_one (R := k) h1
    · omega
  exact GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow S o.A o.ab D.F (o.act.toF D) k x (D.m * D.n) ℓ hℓ hℓk (GlobalTheory.T.exists_level_structure_on_torsion p D R b N S s o k x ℓ hℓ hℓp) c hc
    (GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace p D R b N w0 hw S s o k x c hc hcw)

theorem card_ker_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0,
      g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  intro p _ D R _ b N w0 hw S s o k _ _ x
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  have act0 : o.act.act 0 = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  letI : Module (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) :=
    { smul := fun c g => Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c))
      one_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
        rw [map_one, o.act.one, Category.comp_id]; rfl
      mul_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
        rw [map_mul, o.act.mul, Category.assoc]
      smul_zero := fun c => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) = Additive.ofMul 1
        rw [MonObj.one_comp]
      smul_add := fun c g g' => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((g.toMul * g'.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) *
            (g'.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
        rw [MonObj.mul_comp]
      add_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) *
            (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)))
        rw [map_add, o.act.add, MonObj.comp_mul]
      zero_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
        rw [map_zero, act0, MonObj.comp_one] }
  have hsm : ∀ (c : 𝓞 D.F) (g : Additive (Over.mk x ⟶ o.A)),
      c • g = Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) := fun _ _ => rfl
  have hmax : w0.IsMaximal := hw.1
  have hne : w0 ≠ ⊥ := by
    intro h0
    have hp : ((p : ℕ) : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h0, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  have hdiv : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive (Over.mk x ⟶ o.A) => c • g) := by
    intro c hc g
    set n := Ideal.absNorm (Ideal.span {c}) with hn
    have hn0 : 0 < n := by
      rw [hn, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc
    have hmem : ((n : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g', hg'⟩ := GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme S o.A o.ab k x n hn0 g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, hc', Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl

  have hT : ∀ I : Ideal (𝓞 D.F), Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      (I : Set (𝓞 D.F))) = Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ I,
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} := by
    intro I
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro h c hc
      have := h ⟨c, hc⟩
      rw [hsm] at this
      exact this
    · intro h c
      rw [hsm]
      exact congrArg Additive.ofMul (h c.1 c.2)

  have hw0nz : w0 ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w0, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w0 ^ H ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w0 ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w0 ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 D.F))) = ⟨w0, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w0 ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w := by
    intro w hwm _ hww hcw
    apply hww
    have h1 : w0 ^ H ≤ w := by rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hcw
    exact (hmax.eq_of_le hwm.ne_top (hwm.isPrime.le_of_pow_le h1)).symm
  have hcount := card_ker_elt hw o k x c hc0 hcw
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 D.F ⧸ w0) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

  have hTH : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) = Nat.card (𝓞 D.F ⧸ w0) ^ (H * (D.m * D.n)) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, ← hcount]
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBy_iff, hsm]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

  have hq : 1 < Nat.card (𝓞 D.F ⧸ w0) := by
    have hfin : Finite (𝓞 D.F ⧸ w0) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w0
    exact Finite.one_lt_card

  have hTHfin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F)) ≤
      Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w0
  haveI : Module.Finite (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) =
      Nat.card (𝓞 D.F ⧸ w0) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField D.F _ w0 h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * (D.m * D.n) = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = D.m * D.n := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [← hT, hT1, he']

end GlobalTheory.UPel.HT.EtLev.GeoCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationConstantOfLogKodairaSpencerMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartConst

theorem exists_derivation_top {R : Type} [CommRing R] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤), ⇑D' = fun r =>
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)) := by
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun x y => by rw [map_add, map_add, map_add] }) fun a b => ?_, rfl⟩
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a * b))) =
    a • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)) +
      b • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a))
  rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, e, e, smul_eq_mul, smul_eq_mul]

theorem valR_mem_maximalIdeal {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (g : Sp R ⟶ X) (U : X.Opens)
    (hU : ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) (hf : g (closedPoint R) ∉ X.basicOpen f) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U ⊤ hU).hom f) ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  rw [e] at h1
  have h2 := (Sp R).basicOpen_of_isUnit h1
  have h3 := Scheme.basicOpen_appLE g ⊤ U hU f
  have h4 : closedPoint R ∈ (⊤ : (Sp R).Opens) ⊓ g ⁻¹ᵁ X.basicOpen f := by
    rw [← h3]
    exact h2.ge trivial
  exact hf h4.2

theorem isConstAlong_of_ks_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc U n v A hv hb hA D Θ m hm x hxi hxU hxm hKS hΘ k _ m' d ξ x' hξ hx'x t P gam
    hEt hId hBd ⟨φ⟩ hMon hPart hU DR a hDR ha ρ hρ
  subst hξ hx'x
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  have : CharZero k := GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  have hfac := GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.LocReg.BasisPull.exists_basis_pull E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hb
  have hab := GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ hBd
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (Submodule.subtype _) (by simp)
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom_inv_id_apply r
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom
      (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r) := fun r => dif_pos hU
  have hch : ∀ r, valR (ξ ≫ genι Y) U.1 r = GlobalTheory.LocReg.chartHom Y U ξ hx r := fun r => by
    have h := GlobalTheory.CechKSSmul.valR_spMap_chart U (GlobalTheory.LocReg.chartHom Y U ξ hx) r
    rwa [← hfac] at h
  have happ : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) =
      ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom := RingHom.ext fun r => by
    rw [RingHom.comp_apply, ← hch, hval, e]
  obtain ⟨D', hD'⟩ := exists_derivation_top DR
  have hV : (⊤ : (Sp (ChartRing k m' d)).Opens) ⊓ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) ≤
      (ξ ≫ genι Y) ⁻¹ᵁ interior Y := by
    intro p hp
    have h1 : p ∈ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) := hp.2
    have h2 := basicOpen_eq_of_affine (R := CommRingCat.of (ChartRing k m' d)) (∏ i, bdParam k m' d i)
    have h3 : p ∈ PrimeSpectrum.basicOpen (∏ i, bdParam k m' d i) := h2.le h1
    have h4 : ξ p ∉ genBd Y := fun h => h3 ((hBd p).1 h)
    rw [mem_genBd_iff, not_not, ← coe_interior] at h4
    exact h4
  have hK := GlobalTheory.T.cechKodairaSpencer_pullback_semiAbelianMap E H Y.X (Sp (ChartRing k m' d)) Y.t t (ξ ≫ genι Y) φ (interior Y) _ U
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m' d)).affineOpens) hU hV n v vR hv hvR
    (fun i => by rw [hcomp i, happ]) D.1 D' (fun r => by
      rw [hD']
      show (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (DR
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r))) =
        ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom (D.1 r)
      rw [← hval, hDR, hval, e]) Θ hKS
  rw [hD'] at hK
  exact GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart E H k m' d t P (fun i => gam i) hMon hlin hab n vR hvR hbR DR a ha _ hK
    (fun a b => valR_mem_maximalIdeal (ξ ≫ genι Y) U.1 hU (Θ a b) (hxm _ (hΘ a b))) ρ hρ

end GlobalTheory.ChartConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ d f hf
  haveI := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have htR : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t =
      spMap ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) := by
    rw [ht]; exact (GlobalTheory.Cris.spMap_comp _ _).symm
  have ht₀ : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫
      (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) := by
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
    have : (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp (algebraMap k (TrivSqZeroExt k (Fin d → k))) = RingHom.id k := by
      ext a; simp
    rw [this]
    simp [spMap]
  have h1 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h2 := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFil_htObject p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h3 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h4 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_isotropic_polarisation p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h5 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_lie_condition p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have key := GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration p D R b N hNp (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom hsurj (GlobalTheory.FODef.sqZero k (Fin d → k))
    ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) t htR ht₀ o₀ (GlobalTheory.HTGlue.glueFil o₀.A f)
  obtain ⟨o, m, hm⟩ := key h1 h2 h3 h4 h5
  refine ⟨o, m, fun x hx => ?_⟩
  obtain ⟨e, he, hce⟩ := GlobalTheory.HTGlue.exists_mem_glueFil o₀.A o₀.ab f hx
  unfold GlobalTheory.FODef.IsFilLiftV
  refine ⟨e, ?_, hce⟩
  rw [hm]; exact he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, t = spMap β := ⟨(Spec.preimage t).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k t o₀
  obtain ⟨f, hfKS, huniq⟩ := GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim p D R b N hN hNp k t o₀ β hβ φ hφ
  refine ⟨f, fun j => GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k t o₀ β hβ φ hφ (f j) (hfKS j), fun o' m' => ?_⟩
  obtain ⟨g, hgKS, hg⟩ := GlobalTheory.T.harrisTaylor_firstOrder_hodge_eq_kodairaSpencer_graph p D R b N hN hNp k t o₀ β hβ φ hφ o' m'
  obtain ⟨c, hc, hcu⟩ := huniq g hgKS
  refine ⟨c, fun x hx => ?_, fun c' hc' => hcu c' fun x hx => ?_⟩
  · refine (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).2 ?_
    rw [← neg_sub]; exact neg_mem (hc x hx)
  · have := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hx (g x) _ (hg x hx)).1 (hc' x hx)
    rw [← neg_sub]; exact neg_mem this

end GlobalTheory.HTCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_family_from_regular_base_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  first | exact @GlobalTheory.UCanon.FamFrom.main | exact GlobalTheory.UCanon.FamFrom.main | (intros; apply GlobalTheory.UCanon.FamFrom.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectExistsCharZeroLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_exists_charZero_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K) (cV : SiegPre g n (zetaAway n) (spMap βV)), Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  first | exact @GlobalTheory.SiegLift0.exists_lift_domain | exact GlobalTheory.SiegLift0.exists_lift_domain | (intros; apply GlobalTheory.SiegLift0.exists_lift_domain <;> assumption)
end

