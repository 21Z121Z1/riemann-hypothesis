import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
section
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

def resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A : ∀ i, Subgroup (G i)) :
    Subgroup (∀ i, G i) where
  carrier := {g | {i | g i ∉ A i}.Finite}
  one_mem' := by
    have : {i | (1 : ∀ i, G i) i ∉ A i} = ∅ := by
      ext i; simp [one_mem]
    simp only [Set.mem_setOf_eq, this, Set.finite_empty]
  mul_mem' := by
    intro a b ha hb
    refine (Set.Finite.union ha hb).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (mul_mem h.1 h.2)
  inv_mem' := by
    intro a ha
    refine Set.Finite.subset ha (fun i hi => ?_)
    simpa using hi

theorem pi_le_resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A U : ∀ i, Subgroup (G i))
    (h : {i | A i ≠ U i}.Finite) : Subgroup.pi Set.univ U ≤ resPi A := by
  intro g hg
  refine Set.Finite.subset h (fun i hi hAU => hi ?_)
  rw [hAU]
  exact hg i (Set.mem_univ i)

theorem exists_finset_cosets {G : Type} [Group G] (K L : Subgroup G) (h : L.relIndex K ≠ 0) :
    ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ L := by
  haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : G)), ?_⟩
  intro k hk
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨k, hk⟩)), ?_⟩
  have h1 : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ L.subgroupOf K) : K) :
      K ⧸ L.subgroupOf K) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.1 h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem double_cosets_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : K0.relIndex KA ≠ 0)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ KA, g = γ * a * κ) :
    ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨T, hT⟩ := exists_finset_cosets KA K0 h
  refine ⟨Finset.image₂ (· * ·) S T, fun g => ?_⟩
  obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
  obtain ⟨t, ht, htκ⟩ := hT κ hκ
  exact ⟨a * t, Finset.mem_image₂_of_mem ha ht, γ, hγ, t⁻¹ * κ, htκ, by group⟩

theorem finite_conj_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : KA.relIndex K0 ≠ 0) (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ KA}.Finite) (a : G) :
    {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_cosets K0 KA h
  have hpiece : ∀ t ∈ T, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ * a) ∈ KA}.Finite := by
    intro t _
    by_cases hne : ∃ γ₀, γ₀ ∈ Γ ∧ a⁻¹ * γ₀ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ₀ * a) ∈ KA
    · obtain ⟨γ₀, hγ₀, -, h₀⟩ := hne
      refine ((hF a).image (fun δ => γ₀ * δ)).subset ?_
      rintro γ ⟨hγ, -, h₁⟩
      refine ⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, ?_⟩, by group⟩
      have := KA.mul_mem (KA.inv_mem h₀) h₁
      convert this using 1
      group
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨h1, h2, h3⟩
      exact hne ⟨γ, h1, h2, h3⟩
  refine (T.finite_toSet.biUnion hpiece).subset ?_
  rintro γ ⟨hγ, hk⟩
  obtain ⟨t, ht, htk⟩ := hT _ hk
  exact Set.mem_biUnion ht ⟨hγ, hk, htk⟩

theorem invVol_subgroupOf {G : Type} [Group G] (R K L : Subgroup G) (hK : K ≤ R) (hL : L ≤ R) :
    invVol (K.subgroupOf R) (L.subgroupOf R) = invVol K L := by
  simp only [invVol, Subgroup.relIndex_subgroupOf hK, Subgroup.relIndex_subgroupOf hL]

theorem tsum_quot_out {Y : Type} (r : Y → Y → Prop) (s : Setoid Y) (hr : ∀ a b, r a b ↔ s.r a b)
    (F : Y → ℝ≥0∞) : ∑' o : Quot r, F o.out = ∑' o : Quotient s, F o.out := by
  obtain rfl : r = s.r := by
    funext a b
    exact propext (hr a b)
  rfl

theorem stabilizer_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] {X : ι → Type}
    [∀ i, MulAction (G i) (X i)] (x : ∀ i, X i) :
    MulAction.stabilizer (∀ i, G i) x =
      Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_pi, funext_iff]

theorem stabilizer_res {P : Type} [Group P] (R : Subgroup P) {Y : Type} [MulAction P Y] (y : Y) :
    MulAction.stabilizer R y = (MulAction.stabilizer P y).subgroupOf R := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]

end GlobalTheory.HL

namespace GlobalTheory.HL

theorem mass_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  intro ι G _ X _ A H _ φ hinj hres hdc hfin x0 hcomm hae
  set R := resPi A with hRdef
  let φ' : H →* R := φ.codRestrict R hres
  have hφ' : ∀ h, ((φ' h : R) : ∀ i, G i) = φ h := fun h => rfl
  set Γ : Subgroup R := φ'.range with hΓ
  set KA : Subgroup R := (Subgroup.pi Set.univ A).subgroupOf R with hKA
  set K0 : Subgroup R := MulAction.stabilizer R x0 with hK0
  have hAR : Subgroup.pi Set.univ A ≤ R := pi_le_resPi A A (by simp)
  have hstab0 : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i)) ≤ R :=
    pi_le_resPi A _ hae
  have hK0' : K0 = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i))).subgroupOf R := by
    rw [hK0, stabilizer_res, stabilizer_pi]
  have hpi := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) A
    (by simpa [eq_comm] using hae) hcomm
  have hc1 : K0.relIndex KA ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hAR]; exact hpi.1
  have hc2 : KA.relIndex K0 ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hstab0]; exact hpi.2.1
  have hDC : ∃ S : Finset R, ∀ g : R, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
    refine double_cosets_transfer Γ KA K0 hc1 ?_
    obtain ⟨S, hSR, hS⟩ := hdc
    refine ⟨S.subtype (· ∈ R), fun g => ?_⟩
    obtain ⟨s, hs, h, k, hk, hg⟩ := hS g g.2
    have hkR : k ∈ R := hAR (fun i _ => hk i)
    refine ⟨⟨s, hSR s hs⟩, by simpa using hs, φ' h, ⟨h, rfl⟩, ⟨k, hkR⟩, ?_, ?_⟩
    · simpa [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi] using hk
    · ext1; simpa [hφ'] using hg
  have hFin : ∀ a : R, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
    refine finite_conj_transfer Γ KA K0 hc2 (fun a => ?_)
    refine ((hfin a a.2).image φ').subset ?_
    rintro γ ⟨⟨h, rfl⟩, hγ⟩
    refine ⟨h, fun i => ?_, rfl⟩
    have := hγ
    simp only [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, forall_const] at this
    simpa [hφ'] using this i
  obtain ⟨V0, hV0, hmass⟩ := GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets Γ K0 hDC hFin
  refine ⟨V0, hV0, fun x hx hxae => ?_⟩

  have hAx : {i | A i ≠ MulAction.stabilizer (G i) (x i)}.Finite := by
    refine (hae.union hxae).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (by rw [h.1, h.2])
  have hstabx : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) ≤ R :=
    pi_le_resPi A _ hAx
  have hSx : MulAction.stabilizer R x =
      (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i))).subgroupOf R := by
    rw [stabilizer_res, stabilizer_pi]
  have hpx := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i))
    (fun i => MulAction.stabilizer (G i) (x i))
    (hxae.subset (fun i hi h => hi (by rw [h]))) hx
  have d1 : K0.relIndex (MulAction.stabilizer R x) ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstabx]; exact hpx.1
  have d2 : (MulAction.stabilizer R x).relIndex K0 ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstab0]; exact hpx.2.1
  have hm := hmass (∀ i, X i) x d1 d2
  have hvol : invVol K0 (MulAction.stabilizer R x) =
      ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i)) := by
    rw [hK0', hSx, invVol_subgroupOf R _ _ hstab0 hstabx]; exact hpx.2.2
  rw [← hvol, ← hm]
  have hφinj : Function.Injective φ' := fun a b hab => hinj (congrArg Subtype.val hab)
  have horb : ∀ y : ∀ i, X i, ((∀ i, ∃ g : G i, g • x i = y i) ∧ {i | y i ≠ x i}.Finite) ↔
      y ∈ MulAction.orbit R x := by
    intro y
    constructor
    · rintro ⟨hall, hf⟩
      let g : ∀ i, G i := fun i => if y i = x i then 1 else Classical.choose (hall i)
      have hgR : g ∈ R := by
        refine hf.subset (fun i hi hyx => hi ?_)
        simp only [g, hyx, if_true]
        exact one_mem _
      refine ⟨⟨g, hgR⟩, funext fun i => ?_⟩
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      by_cases hyx : y i = x i
      · simp [g, hyx]
      · simp only [g, hyx, if_false]
        exact Classical.choose_spec (hall i)
    · rintro ⟨g, rfl⟩
      refine ⟨fun i => ⟨(g : ∀ i, G i) i, by dsimp only; rw [Subgroup.smul_def, Pi.smul_apply']⟩, ?_⟩
      refine ((g.2 : {i | (g : ∀ i, G i) i ∉ A i}.Finite).union hAx).subset (fun i hi => ?_)
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
      apply hi
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      have := h.1
      rw [h.2] at this
      exact this
  have henc : ∀ y : ∀ i, X i, {h : H | φ h • y = y}.encard =
      ((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard := by
    intro y
    rw [← hφinj.encard_image]
    congr 1
    ext γ
    simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [Subgroup.smul_def]; exact hh⟩
    · rintro ⟨⟨h, rfl⟩, hh⟩
      exact ⟨h, by rw [Subgroup.smul_def] at hh; exact hh, rfl⟩
  refine (tsum_congr fun o => ?_).trans (tsum_quot_out _ (MulAction.orbitRel Γ (∀ i, X i)) ?_ (fun y =>
    if y ∈ MulAction.orbit R x then
      ((((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard : ℝ≥0∞))⁻¹ else 0))
  · beta_reduce
    simp only [henc, horb]
  · intro a b
    rw [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨φ' h, h, rfl⟩⁻¹, ?_⟩
      dsimp only
      simp [Subgroup.smul_def, hφ']
    · rintro ⟨⟨γ, h, rfl⟩, hγ⟩
      refine ⟨h⁻¹, ?_⟩
      rw [← hγ]
      dsimp only
      simp [Subgroup.smul_def, hφ']

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise
section
open NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NearLowerCompare

open Formalism.MainNotions.S GlobalTheory.Count Formalism.HN

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

end General

variable (I : AutInst)

theorem lamX_isLattice (x : I.GA) : Submodule.IsLattice I.E (lamX I x) := by
  have h := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  have e : lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
    ext y
    rw [GlobalTheory.Count.Test.mem_lamX, ← e1]
    exact Iff.rfl
  rw [e]; exact h

theorem frm_isUnit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h : ∀ v, IsUnit (I.P v * uMat (x.1 v)) := fun v => (I.P_unit v).mul (Units.isUnit _)
  rw [← Matrix.isUnit_iff_isUnit_det]
  unfold frm
  split_ifs
  · exact h _
  · exact (h _).map (starRingEnd ℂ).mapMatrix

theorem subsingleton_GA (hn : I.n = 0) : Subsingleton I.GA := by
  have : IsEmpty (Fin I.n) := by rw [hn]; infer_instance
  refine ⟨fun a b => Prod.ext (funext fun v => ?_) ?_⟩
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

end GlobalTheory.NearLowerCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacter
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.Pattern

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.Pattern.inPat_mul {Φ : Fin N → Fin N → Prop}
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) {M M' : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) (h' : _root_.GlobalTheory.GLm.InPat Φ M') :
    _root_.GlobalTheory.GLm.InPat Φ (M * M') := by
  intro a b hab
  have hone : (1 : _root_.GlobalTheory.GLq.Mt g N) a b =
      ((1 : _root_.GlobalTheory.GLq.Mt g N) * 1) a b := by rw [one_mul]
  rw [hone, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hac : Φ a c
  · have hcb : ¬ Φ c b := fun hcb => hab (ht a c b hac hcb)
    rw [h' c b hcb]
    by_cases e : c = b
    · subst e; exact absurd hac hab
    · rw [Matrix.one_apply_ne e, mul_zero, mul_zero]
  · rw [h a c hac]
    by_cases e : a = c
    · subst e; rw [h' a b hab]
    · rw [Matrix.one_apply_ne e, zero_mul, zero_mul]

def patSub (g : ℕ) [Fact g.Prime] {N : ℕ} (Φ : Fin N → Fin N → Prop)
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) : Subgroup (Gn g N) where
  carrier := {x | InPat Φ (x : Mt g N)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => inPat_mul ht ha hb
  inv_mem' := by
    intro x hx
    have hp : ∀ k : ℕ, InPat Φ ((x ^ k : Gn g N) : Mt g N) := by
      intro k
      induction k with
      | zero => exact fun _ _ _ => rfl
      | succ k ih => rw [pow_succ]; exact inPat_mul ht ih hx
    have ho : 0 < orderOf x := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    show InPat Φ ((x⁻¹ : Gn g N) : Mt g N)
    rw [this]; exact hp _

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private theorem isUnit_of_inPat_irrefl_trans {Φ : Fin N → Fin N → Prop} (hirr : ∀ a, ¬ Φ a a)
    (htrans : ∀ a b c, Φ a b → Φ b c → Φ a c) {M : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) : IsUnit M := by
  let r : Fin N → ℕ := fun i => (Finset.univ.filter fun j => Φ j i).card
  have hr : ∀ i j, Φ i j → r i < r j := by
    intro i j hij
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp [hirr i]⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact htrans k i j hk hij
  have hbt : Matrix.BlockTriangular M r := by
    intro i j hji
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hji
    rw [h i j (fun hij => absurd (hr i j hij) (not_lt.mpr hji.le)), Matrix.one_apply_ne hne]
  have hblock : ∀ k, Matrix.toSquareBlock M r k = 1 := by
    intro k
    refine Matrix.ext fun i j => ?_
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    have hij : ¬ Φ i.1 j.1 := fun hij => (hr _ _ hij).ne (i.2.trans j.2.symm)
    rw [h _ _ hij]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun h => e (Subtype.ext h))]
  rw [Matrix.isUnit_iff_isUnit_det, hbt.det]
  simp [hblock]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in

theorem _root_.GlobalTheory.GLm.Pattern.pattern_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ)
    (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) →
    (∃ H : Subgroup (_root_.GlobalTheory.GLq.Gn g N),
      (∀ x, x ∈ H ↔ _root_.GlobalTheory.GLm.InPat Φ (x : _root_.GlobalTheory.GLq.Mt g N)) ∧
      Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧
    (∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M) ∧
    ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) →
      ∀ M M' : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M →
        _root_.GlobalTheory.GLm.InPat Φ M' →
        _root_.GlobalTheory.GLm.sumAt E (M * M') =
          _root_.GlobalTheory.GLm.sumAt E M + _root_.GlobalTheory.GLm.sumAt E M' := by
  intro g _ N Φ hirr htrans
  have hunit : ∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M :=
    fun M hM => isUnit_of_inPat_irrefl_trans hirr htrans hM
  refine ⟨⟨_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans, fun x => Iff.rfl, ?_⟩, hunit, ?_⟩
  · have e1 : Nat.card (_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans) =
        Nat.card {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x => ⟨(x.1 : _root_.GlobalTheory.GLq.Mt g N), x.2⟩) ⟨?_, ?_⟩)
      · intro x y hxy
        exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
      · intro M
        exact ⟨⟨(hunit M.1 M.2).unit, M.2⟩, rfl⟩
    let e2 : {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} ≃
        ({p : Fin N × Fin N // Φ p.1 p.2} → ZMod g) :=
      { toFun := fun M p => M.1 p.1.1 p.1.2
        invFun := fun f => ⟨fun a b => if h : Φ a b then f ⟨(a, b), h⟩
            else (1 : _root_.GlobalTheory.GLq.Mt g N) a b, fun a b h => by simp [h]⟩
        left_inv := fun M => by
          apply Subtype.ext
          refine Matrix.ext fun a b => ?_
          dsimp only
          split_ifs with h
          · rfl
          · exact (M.2 a b h).symm
        right_inv := fun f => by
          funext p
          simp [p.2] }
    rw [e1, Nat.card_congr e2, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  · intro E hE hEirr M M' hM hM'
    unfold _root_.GlobalTheory.GLm.sumAt
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · rw [Matrix.mul_apply]
      have hne : a ≠ c := by rintro rfl; exact hEirr a hac
      rw [Fintype.sum_eq_add a c hne]
      · rw [hM a a (hirr a), hM' c c (hirr c), Matrix.one_apply_eq, Matrix.one_apply_eq,
          one_mul, mul_one, add_comm]
      · rintro b ⟨hba, hbc⟩
        by_cases hab : Φ a b
        · rw [hM' b c (fun hbc' => hE a b c hab hbc' hac), Matrix.one_apply_ne hbc, mul_zero]
        · rw [hM a b hab, Matrix.one_apply_ne (Ne.symm hba), zero_mul]
    · simp

end GlobalTheory.GLm.Pattern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformiserProductTypePrimes
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.TypePrimeProduct

theorem natPrime_not_mem_of_other (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := by
    have := hZ.map (Int.castRingHom (𝓞 F))
    simpa using this
  obtain ⟨a, b, hab⟩ := hO
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem isUnit_natCast_of_not_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∉ v.asIdeal) :
    IsUnit ((q : ℕ) : v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq] at h
  simpa using h

theorem main_two (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal)
    (hm : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p : ℕ) : v.adicCompletionIntegers F)}) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p * q : ℕ) : v.adicCompletionIntegers F)} ∧
      ((p * q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hqv := natPrime_not_mem_of_other F v hp hq hpq hpv
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]
  · rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hpv

end GlobalTheory.St.G.TypePrimeProduct

open GlobalTheory.St.G.TypePrimeProduct in

theorem GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  intro F _ _ gp hgp hne i v hv hm
  fin_cases i
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 0) (hgp 1) hne hv hm
    exact ⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 1) (hgp 0) hne.symm hv hm
    rw [mul_comm (gp 0)]
    exact ⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩
end

