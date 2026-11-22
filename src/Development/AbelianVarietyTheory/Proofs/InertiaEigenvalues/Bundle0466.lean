import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0005
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualSelmerClassNotKilled
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.DualClass

section Algebra

noncomputable def chr {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n) (y' : B') :
    AddChar B ℂ := (ZMod.stdAddChar (N := n)).compAddMonoidHom (P.flip y')

theorem chr_injective {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n)
    (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Function.Injective (chr P) := by
  intro u v huv
  refine sub_eq_zero.1 (h _ fun y => ?_)
  rw [map_sub, sub_eq_zero]
  exact ZMod.injective_stdAddChar (DFunLike.congr_fun huv y)

theorem card_addChar (B : Type) [AddCommGroup B] [Finite B] : Nat.card (AddChar B ℂ) = Nat.card B := by
  classical
  have := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card (α := AddChar B ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

theorem card_le_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Nat.card B' ≤ Nat.card B := by
  rw [← card_addChar B]
  exact Nat.card_le_card_of_injective _ (chr_injective P h)

theorem left_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) (hc : Nat.card B ≤ Nat.card B') (y : B)
    (hy : ∀ y', P y y' = 0) : y = 0 := by
  have hb := (chr_injective P h).bijective_of_nat_card_le (by rw [card_addChar]; exact hc)
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  obtain ⟨y', rfl⟩ := hb.2 ψ
  change ZMod.stdAddChar (P y y') = 1
  rw [hy, AddChar.map_zero_eq_one]

variable {A : Type} [CommRing A]

theorem card_ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] [Finite M] (f : M →ₗ[A] M) :
    Nat.card (LinearMap.ker f) = Nat.card (M ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h3 : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right h3 ?_
  rw [← h1, mul_comm, ← h2]

abbrev Quo (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Type := Y ⧸ LinearMap.range (LinearMap.lsmul A Y c)

abbrev Tor (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Submodule A Y := LinearMap.ker (LinearMap.lsmul A Y c)

variable {n : ℕ} {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']

theorem exists_induced (β : Y →+ Y' →+ ZMod n) (hβ : Bal A β) (c : A) :
    ∃ β₂ : Quo c Y →+ Tor c Y' →+ ZMod n, ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1 := by
  let P : Y →+ Tor c Y' →+ ZMod n := (β.flip.comp (Tor c Y').subtype.toAddMonoidHom).flip
  refine ⟨QuotientAddGroup.lift (LinearMap.range (LinearMap.lsmul A Y c)).toAddSubgroup P ?_, fun y y' => rfl⟩
  rintro _ ⟨y, rfl⟩
  refine AddMonoidHom.mem_ker.2 (AddMonoidHom.ext fun y' => ?_)
  change β (c • y) y'.1 = 0
  have h : c • y'.1 = 0 := y'.2
  rw [hβ, h, map_zero]

theorem perf_induced [NeZero n] [Finite Y] [Finite Y'] (β : Y →+ Y' →+ ZMod n) (hβ : Perf A β) (c : A)
    (β₂ : Quo c Y →+ Tor c Y' →+ ZMod n) (h : ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1) : Perf A β₂ := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Finite (Quo c Y') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hr : ∀ y', (∀ y, β₂ y y' = 0) → y' = 0 := fun y' hy =>
    Subtype.ext (hβ.2.2 _ fun y => by rw [← h, hy])
  refine ⟨fun a y y' => ?_, left_of_right β₂ hr ?_, hr⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, h, h, hβ.1]
    rfl
  · obtain ⟨γ, hγ⟩ := exists_induced (A := A) β.flip (fun a y' y => (hβ.1 a y y').symm) c
    rw [← card_ker_eq_coker, card_ker_eq_coker (LinearMap.lsmul A Y' c)]
    exact card_le_of_right γ fun y hy => Subtype.ext (hβ.2.1 _ fun y' => by
      have := hy (Submodule.Quotient.mk y')
      rwa [hγ] at this)

theorem smul_mem_range [Finite Y] {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : Nat.card (LinearMap.ker (matAct (M := Y) Φ)) ≤ Nat.card (LinearMap.ker (matAct (M := Quo c Y) Φ)))
    (w : Fin a → Y) : c • w ∈ LinearMap.range (matAct (M := Y) Φ) := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [card_ker_eq_coker, card_ker_eq_coker] at h
  let f : (Fin a → Y) →ₗ[A] (Fin a → Quo c Y) := (Submodule.mkQ _).compLeft (Fin a)
  have hf : LinearMap.range (matAct (M := Y) Φ) ≤ (LinearMap.range (matAct (M := Quo c Y) Φ)).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, funext fun b => ?_⟩
    simp [f, matAct, map_sum]
  have hs : Function.Surjective (Submodule.mapQ _ _ f hf) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose u hu using fun b => Submodule.Quotient.mk_surjective _ (x b)
    exact ⟨Submodule.Quotient.mk u, by rw [Submodule.mapQ_apply]; exact congrArg _ (funext hu)⟩
  have : Finite ((Fin a → Y) ⧸ LinearMap.range (matAct (M := Y) Φ)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hb := hs.bijective_of_nat_card_le h
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero, Submodule.mapQ_apply]
  have h0 : f (c • w) = 0 := funext fun b => (Submodule.Quotient.mk_eq_zero _).2 ⟨w b, rfl⟩
  rw [h0, Submodule.Quotient.mk_zero]

theorem mul_eq_zero_of_range (β : Y →+ A →+ ZMod n) (hβ : Perf A β) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : ∀ w : Fin a → Y, c • w ∈ LinearMap.range (matAct (M := Y) Φ)) (y₀ : Fin a → A) (h0 : Matrix.vecMul y₀ Φ = 0)
    (j : Fin a) : c * y₀ j = 0 := by
  refine hβ.2.2 _ fun w => ?_
  obtain ⟨x, hx⟩ := h (Pi.single j w)
  have h1 : ∑ b, y₀ b • matAct Φ x b = 0 := by
    change ∑ b, y₀ b • ∑ k, Φ b k • x k = 0
    simp only [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h2 : ∑ b, y₀ b * Φ b k = 0 := congrFun h0 k
    rw [← Finset.sum_smul, h2, zero_smul]
  rw [hx, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  have h3 : (c * y₀ j) • w = 0 := by
    rw [mul_comm, mul_smul]
    simpa using h1
  have h4 := hβ.1 (c * y₀ j) w 1
  rw [h3, smul_eq_mul, mul_one] at h4
  rw [← h4]
  simp

end Algebra

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host))

theorem card_selOn {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (Z : GE N → Matrix (Fin D.R.r) (Fin a) A)
    (h : Univ bkP i s κ Q Φ Z) (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] :
    Nat.card (LinearMap.ker (matAct (M := Y) Φ)) = Nat.card (selOn bkP i (Tgl i s) κ Y Q) := by
  obtain ⟨h1, h2, h3⟩ := h Y
  choose z hz hz' using fun x : LinearMap.ker (matAct (M := Y) Φ) => h1 x.1 x.2
  refine Nat.card_eq_of_bijective (fun x => ⟨_, hz' x⟩) ⟨fun x x' hx => ?_, fun q => ?_⟩
  · have e := (Submodule.Quotient.eq _).1 (congrArg Subtype.val hx)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 e
    refine sub_eq_zero.1 (Subtype.ext (h2 _ (x - x').2 ⟨m, fun g => ?_⟩))
    rw [← hm g]
    change _ = (z x).1 g - (z x').1 g
    rw [hz, hz]
    funext b
    simp [rect, smul_sub]
  · obtain ⟨q, hq⟩ := q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, m, hm⟩ := h3 y.1 ⟨y, rfl, hq⟩
    refine ⟨⟨x, hx⟩, Subtype.ext (Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)))⟩
    rw [← hm g]
    change y.1 g - (z ⟨x, hx⟩).1 g = _
    rw [hz]

omit [Algebra (X.O0 i) A] in

theorem card_invariants_torsion_submodule {Γ O : Type} [Group Γ] [CommRing O] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ)
    (U : Subgroup Γ) (Y' : Type) [AddCommGroup Y'] [Module A Y'] (c : A)
    (h : ∀ m, (∀ g ∈ U, repOn ρ κ Y' g m = m) → c • m = 0) :
    Nat.card (H0 ((repOn ρ κ (Tor c Y')).comp U.subtype)) = Nat.card (H0 ((repOn ρ κ Y').comp U.subtype)) := by
  refine Nat.card_eq_of_bijective (fun m => ⟨(Tor c Y').subtype.compLeft (Fin r) m.1, fun g => ?_⟩)
    ⟨fun m m' hm => ?_, fun m => ?_⟩
  · exact (repOn_map ρ κ (Tor c Y').subtype g.1 m.1).symm.trans (congrArg _ (m.2 g))
  · exact Subtype.ext (funext fun b => Subtype.ext (congrFun (congrArg Subtype.val hm) b))
  · have h0 := h m.1 fun g hg => m.2 ⟨g, hg⟩
    refine ⟨⟨fun b => ⟨m.1 b, congrFun h0 b⟩, fun g => funext fun b => Subtype.ext ?_⟩, rfl⟩
    exact (congrFun (repOn_map ρ κ (Tor c Y').subtype g.1 _) b).trans (congrFun (m.2 g) b)

theorem exists_not_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  intro D N X bkP i s A _ _ _ _ _ _ κ Q ρ hS hK hD hN hO Y _ _ _ _ _ β hβ a Φ Z hU c t y₀ j ht h0 hne
  by_contra hcon
  have hcob : ∀ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) :=
    fun y hy => by_contra fun h => hcon ⟨y, hy, h⟩
  haveI : NeZero (X.l i ^ (nu X i + 1)) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  letI : TopologicalSpace (Quo (c * t) Y) := ⊥
  haveI : DiscreteTopology (Quo (c * t) Y) := ⟨rfl⟩
  haveI : Finite (Quo (c * t) Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨β₂, hβ₂⟩ := exists_induced β hβ.1 (c * t)
  have hP := perf_induced β hβ (c * t) β₂ hβ₂
  obtain ⟨-, e1⟩ := hO Y A β hβ
  obtain ⟨f2, e2⟩ := hO (Quo (c * t) Y) (Tor (c * t) A) β₂ hP
  have hsub : DualCl bkP i s κ ρ β Q ⊆ h1Map ρ κ⁻¹ (Tor (c * t) A).subtype '' DualCl bkP i s κ ρ β₂ Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y₂, hy₂, m, hm⟩ := GlobalTheory.T.dualSelmerClass_from_coeffsKilledBy_mul D N X bkP i s A κ Q ρ hS hK hD hN Y A (Quo (c * t) Y) (Tor (c * t) A) β β₂
      (Submodule.mkQ _) (Tor (c * t) A).subtype c t hβ.1 hP.1 (Submodule.mkQ_surjective _) (Submodule.injective_subtype _)
      (fun y' h => ⟨⟨y', h⟩, rfl⟩) hβ₂ ht y hy (hcob y hy)
    exact ⟨_, ⟨y₂, hy₂, rfl⟩, Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, hm⟩))⟩
  have hfin : (DualCl bkP i s κ ρ β₂ Q).Finite := f2
  have hle : Nat.card (DualCl bkP i s κ ρ β Q) ≤ Nat.card (DualCl bkP i s κ ρ β₂ Q) :=
    (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  have hprod : ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ (Tor (c * t) A)).comp (DecV N v).subtype)) =
      ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ A).comp (DecV N v).subtype)) :=
    Finset.prod_congr rfl fun v hv => card_invariants_torsion_submodule ρ κ⁻¹ (DecV N v) A (c * t) fun m hm => by
      rw [mul_smul, ht v (Or.inr hv) m hm, smul_zero]
  refine hne (mul_eq_zero_of_range β hβ Φ (c * t) (smul_mem_range Φ (c * t) ?_) y₀ h0 j)
  rw [card_selOn bkP i s κ Q Φ Z hU, card_selOn bkP i s κ Q Φ Z hU, e1, e2, hprod]
  exact Nat.mul_le_mul_right _ hle

end GlobalTheory.NewPrime.DualClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobInvMulMemIner
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

noncomputable section

namespace GlobalTheory.FrobLiftUnr

variable {l : ℕ} [Fact l.Prime]

theorem qK_bot : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (⊥ : IntermediateField ℚ_[l] (Om l)) = l := by
  have hK : FiniteDimensional ℚ_[l] (⊥ : IntermediateField ℚ_[l] (Om l)) := inferInstance
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.eK_mul_fK l ⊥ hK
  rw [IntermediateField.finrank_bot] at h
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK l ⊥ hK, Nat.eq_one_of_mul_eq_one_left h, pow_one]

theorem exists_frob : ∃ Φ : GQ l, ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1 := by
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l)))
    inferInstance
  refine ⟨σ.restrictScalars ℚ_[l], fun x hx => ?_⟩
  have h := hσ x hx
  rw [qK_bot] at h
  exact h

theorem mem_GK_qlExt (Φ : GQ l) : Φ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  unfold GK
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact Φ.commutes r

theorem max_unramified_le_unramified_ext (K' : FinExt l) :
    K0 K' ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l ((⊥ : IntermediateField ℚ_[l] (Om l))) := by
  refine (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l).trans ?_
  unfold MaximalUnramifiedExtension
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨m, -, hm, hx⟩
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow inferInstance hm hx

theorem max_unramified_eq_adjoin_roots (K' : FinExt l) : ∃ d : ℕ, 0 < d ∧
    K0 K' = IntermediateField.adjoin ℚ_[l] {ζ : Om l | ζ ^ (l ^ d - 1) = 1} := by
  have hQ : FiniteDimensional ℚ_[l] ((⊥ : IntermediateField ℚ_[l] (Om l))) := inferInstance
  have hK' : FiniteDimensional ℚ_[l] K'.1 := K'.2
  have hM : FiniteDimensional ℚ_[l] (K0 K') :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finDim_of_le l hK' (inf_le_left : K0 K' ≤ K'.1)
  obtain ⟨N, hN, hMN⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur hQ hM (max_unramified_le_unramified_ext K')
  have hbot : (⊥ : IntermediateField ℚ_[l] (Om l)) ≤ K0 K' := bot_le
  have hd := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_pos (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) hM
  have heq := ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hbot hd
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_eq_degLK_mul hbot hM)
    (fun x hx => ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hN (hMN hx))
  refine ⟨_, hd, heq.trans ?_⟩
  unfold ReciprocityTheory.DiscreteGroups.LocalClassField.Kn
  rw [qK_bot]
  exact bot_sup_eq _

theorem not_dvd_pow_sub_one {d : ℕ} (hd : 0 < d) : ¬ l ∣ l ^ d - 1 := by
  intro h
  have hp : l.Prime := Fact.out
  have h1 : l ∣ l ^ d := dvd_pow_self l hd.ne'
  have h2 : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem frobenius_lift_eq_on_maxUnramifiedSubfield (K' : FinExt l) (Φ : GQ l) (hΦ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1)
    (σ : ↥(K0 K') →ₐ[ℚ_[l]] ↥(K0 K'))
    (hσ : ∀ x : ↥(K0 K'), ‖((x : ↥(K0 K')) : Om l)‖ ≤ 1 →
      ‖((σ x : ↥(K0 K')) : Om l) - ((x : ↥(K0 K')) : Om l) ^ l‖ < 1)
    (c : ↥(K0 K')) : Φ (c : Om l) = ((σ c : ↥(K0 K')) : Om l) := by
  obtain ⟨d, hd, hM⟩ := max_unramified_eq_adjoin_roots K'
  have hm := not_dvd_pow_sub_one (l := l) hd
  have hm0 : l ^ d - 1 ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero l)
  have key : ((Φ.toAlgHom.restrictScalars ℚ_[l]).comp (K0 K').val : ↥(K0 K') →ₐ[ℚ_[l]] Om l) =
      (K0 K').val.comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hM fun ζ hζ => ?_
    set z : ↥(K0 K') := ⟨ζ, hM ▸ IntermediateField.subset_adjoin ℚ_[l] _ hζ⟩ with hz
    change Φ ζ = ((σ z : ↥(K0 K')) : Om l)
    have hζ' : ζ ^ (l ^ d - 1) = 1 := hζ
    have hn : ‖ζ‖ = 1 := ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ'
    have h1 : (Φ ζ) ^ (l ^ d - 1) = 1 := by rw [← map_pow, hζ', map_one]
    have hz1 : z ^ (l ^ d - 1) = 1 := Subtype.ext hζ'
    have h2 : ((σ z : ↥(K0 K')) : Om l) ^ (l ^ d - 1) = 1 := by
      rw [← IntermediateField.coe_pow, ← map_pow, hz1, map_one]; rfl
    by_contra hne
    have e := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one l hm h1 h2 hne
    have a1 := hΦ ζ hn.le
    have a2 := hσ z hn.le
    have : ‖Φ ζ - ((σ z : ↥(K0 K')) : Om l)‖ < 1 := by
      have eq : Φ ζ - ((σ z : ↥(K0 K')) : Om l) =
          (Φ ζ - ζ ^ l) + (ζ ^ l - ((σ z : ↥(K0 K')) : Om l)) := by ring
      rw [eq]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt a1 ?_)
      rw [norm_sub_rev]; exact a2
    exact absurd e this.ne
  exact congrArg (fun f : ↥(K0 K') →ₐ[ℚ_[l]] Om l => f c) key

end GlobalTheory.FrobLiftUnr

namespace GlobalTheory.FrobLiftUnr

theorem exists_frob_inv_mul_mem_iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl AI _ K' h hN hF hS Fr hFr
  obtain ⟨Φ, hΦ⟩ := exists_frob (l := l)
  refine ⟨⟨Φ, mem_GK_qlExt Φ⟩, fun x _ hx => hΦ x hx, ?_⟩
  intro c
  have hc := hFr c
  have key := frobenius_lift_eq_on_maxUnramifiedSubfield K' Φ hΦ (Pl.PD K').σ (Pl.PD_σ K') c
  have hc' : Pl.actQ Φ (algebraMap ↥(K0 K') Pl.R.B c) =
      algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) :=
    Pl.actQ_Kur Φ ⟨(c : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) c.2⟩
      ⟨(((Pl.PD K').σ c : ↥(K0 K')) : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) ((Pl.PD K').σ c).2⟩ key
  change (Pl.PD _).actB Fr _ = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) at hc
  change (Pl.PD _).actB _ _ = _
  rw [Pl.PD_actB] at hc ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, AlgEquiv.mul_apply]
  change Pl.actQ Φ⁻¹ (Pl.actQ (Fr : GQ l) _) = _
  rw [hc, ← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

end GlobalTheory.FrobLiftUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangula
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

def unipFund (E : Type) [Field E] [NumberField E] (n : ℕ) : Set (NA E n) :=
  {u | ∀ i j : Fin n, i < j → ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E}

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ratGL_mem_NA {γ : GL (Fin n) E} (hγ : γ ∈ GlobalTheory.SmGL.unipB E (Fin n)) : ratGL E n γ ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [ratGL, h1 i j hij]
  · simp [ratGL, h2 i]

theorem exists_fundamentalDomain_NE (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (NA E n)) [ν.IsHaarMeasure] : ∃ D : Set (NA E n),
    IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  classical
  have hfd : IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) (unipFund E n) ν := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · refine MeasurableSet.nullMeasurableSet ?_
      have : unipFund E n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
          (fun u : NA E n => ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) ⁻¹'
            GroundTheory.Global.fundamentalSet E := by
        ext u; simp [unipFund]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      refine (Continuous.measurable ?_) (GroundTheory.Global.measurableSet_fundamentalSet E)
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
    · intro x
      obtain ⟨γ, ⟨hγ, hγD⟩, huniq⟩ := GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet E n (x : GA E n) x.2
      refine ⟨⟨⟨ratGL E n γ, ratGL_mem_NA hγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)⟩,
        fun i j hij => hγD i j hij, ?_⟩
      intro g hg
      obtain ⟨γ', hγ', hγ'g⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
      have he : γ' = γ := huniq γ' ⟨hγ', fun i j hij => by
        have := hg i j hij
        rw [hγ'g]; exact this⟩
      apply Subtype.ext; apply Subtype.ext
      change ((g : NA E n) : GA E n) = ratGL E n γ
      rw [← hγ'g, he]
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hG : Countable ((NE E n).subgroupOf (NA E n)) := by
    have h : ∀ g : (NE E n).subgroupOf (NA E n), ∃ γ : GL (Fin n) E, ratGL E n γ = ((g : NA E n) : GA E n) :=
      fun g => by
        obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
        exact ⟨γ, hγ⟩
    choose f hf using h
    have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    have : Countable (GL (Fin n) E) :=
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E))
        fun a b h => Units.ext h
    exact Function.Injective.countable (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (by rw [← hf a, ← hf b, hab]))
  have hinv : SMulInvariantMeasure ((NE E n).subgroupOf (NA E n)) (NA E n) ν :=
    ⟨fun g s _ => by
      have : (fun x : NA E n => g • x) = fun x => (g : NA E n) * x := rfl
      show ν ((fun x => g • x) ⁻¹' s) = ν s
      rw [this]; exact measure_preimage_mul ν (g : NA E n) s⟩
  refine ⟨unipFund E n, hfd, pos_iff_ne_zero.2 (hfd.measure_ne_zero (NeZero.ne ν)), ?_⟩
  set C : Set (Ad E) := closure (GroundTheory.Global.fundamentalSetInfinite E) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E)) with hCdef
  have hC : IsCompact C := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite E).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles E)
  set K : Set (GA E n) := {g : GA E n | g ∈ NA E n ∧ ∀ i j : Fin n, i < j →
    (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} with hKdef
  have hK : IsCompact ((Subtype.val : NA E n → GA E n) ⁻¹' K) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype,
      Set.inter_eq_left.2 (fun g hg => hg.1)]
    exact GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact E n C hC
  refine (measure_mono fun u hu => ?_).trans_lt hK.measure_lt_top
  refine ⟨u.2, fun i j hij => ?_⟩
  have h := hu i j hij
  exact ⟨subset_closure h.1, h.2⟩

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LiftKur

theorem exists_gal_fix_Kur_map : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  intro l _ x y hy
  haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)
  haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _
  have hx : IsIntegral ↥(MaximalUnramifiedExtension l) x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm
  refine ⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩
  · intro z hz
    show τ z = z
    exact τ.commutes ⟨z, hz⟩
  · show τ x = y
    exact hτ

end GlobalTheory.LiftKur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_weight_form : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ β, IsInvForm a β := by
  first | exact @GlobalTheory.InvFormBdd.exists_isInvForm | exact GlobalTheory.InvFormBdd.exists_isInvForm | (intros; apply GlobalTheory.InvFormBdd.exists_isInvForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  first | (exact @GlobalTheory.FlatKummer.exists_kummer_flat) | (exact GlobalTheory.FlatKummer.exists_kummer_flat) | (intros; apply GlobalTheory.FlatKummer.exists_kummer_flat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiOperatorEtalePhiGammaModuleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_operator_etale_phiGamma_module : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  first | exact @GlobalTheory.psiD_exists | exact GlobalTheory.psiD_exists | (intros; apply GlobalTheory.psiD_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallSubgroupCocycleFormNeZeroStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smallSubgroup_cocycleForm_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  first | exact @GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero | exact GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero | (intros; apply GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero <;> assumption)
end

