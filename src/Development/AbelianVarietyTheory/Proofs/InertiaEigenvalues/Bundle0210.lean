import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnramA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.SeqCount

open Formalism.NG ReciprocityTheory.ChartRestriction.T2

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M]

theorem exists_pow_smul_eq {ϖ : O} (hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m) (n : ℕ) (m : M) :
    ∃ m' : M, ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih m
    obtain ⟨b, hb⟩ := hdiv a
    exact ⟨b, by rw [pow_succ, mul_smul, hb, ha]⟩

theorem lev_val_injective {c : O} : Function.Injective (Lev.val : Lev M c → M) :=
  fun _ _ h => Lev.ext h

def levelCocycleToModuleCocycle (ρ : Representation O G M) (c : O) : Z1 (levRep ρ c) →ₗ[O] coZ1s ρ where
  toFun f := ⟨fun g => (f.1 g).val, fun g h => by
    have := ((mem_Z1_iff_cocycle _ _).1 f.2).2 g h
    show (f.1 (g * h)).val = (f.1 g).val + ρ g (f.1 h).val
    rw [this, Lev.val_add, levRep_val]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelH1ToModuleH1 (ρ : Representation O G M) (c : O) : H1 (levRep ρ c) →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (levelCocycleToModuleCocycle ρ c) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    exact ⟨m.val, funext fun g => by
      have h2 : f.1 g = levRep ρ c g m - m := hm g
      show ρ g m.val - m.val = (f.1 g).val
      rw [h2]; rfl⟩)

theorem valuation_H1_mk (ρ : Representation O G M) (c : O) (f : Z1 (levRep ρ c)) :
    levelH1ToModuleH1 ρ c (Submodule.Quotient.mk f) = Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) := rfl

theorem valuation_H1_mem (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : levelH1ToModuleH1 ρ c x ∈ HcLC ρ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨levelCocycleToModuleCocycle ρ c f, ?_, rfl⟩
  show IsLocallyConstant (fun g => (f.1 g).val)
  have h1 : IsLocallyConstant f.1 := (IsLocallyConstant.iff_continuous f.1).2 ((mem_Z1_iff_cocycle _ _).1 f.2).1
  exact h1.comp _

theorem smul_valuation_H1 (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : c • levelH1ToModuleH1 ρ c x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [valuation_H1_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨0, funext fun g => ?_⟩
  show ρ g 0 - 0 = c • (f.1 g).val
  rw [Lev.smul_val, map_zero, sub_zero]

def phi (ρ : Representation O G M) (c : O) :
    H1 (levRep ρ c) →ₗ[O] LinearMap.ker (c • LinearMap.id : HcLC ρ →ₗ[O] HcLC ρ) :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (HcLC ρ) (levelH1ToModuleH1 ρ c) (valuation_H1_mem ρ c)) (fun x => by
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact Subtype.ext (smul_valuation_H1 ρ c x))

theorem phi_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m)
    (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) : Function.Surjective (phi ρ c) := by
  rintro ⟨⟨y, hy⟩, hk⟩
  obtain ⟨z, hz, rfl⟩ := hy
  have hk' : c • (Submodule.mkQ _ z : H1z ρ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.1 hk)
    simpa using this
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk'
  obtain ⟨m, hm⟩ := hk'
  obtain ⟨m', hm'⟩ := hdiv m
  have hz2 : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := z.2
  have hzlc : IsLocallyConstant (z.1 : G → M) := hz
  let w : G → M := fun g => z.1 g - (ρ g m' - m')
  have hw : ∀ g, c • w g = 0 := fun g => by
    have h1 : ρ g m - m = c • z.1 g := congrFun hm g
    show c • (z.1 g - (ρ g m' - m')) = 0
    rw [smul_sub, smul_sub, ← map_smul (ρ g) c m', hm', h1, sub_self]
  have hwlc : IsLocallyConstant w := hzlc.sub ((hlc m').sub (IsLocallyConstant.const m'))
  have hwc : ∀ g h, w (g * h) = w g + ρ g (w h) := fun g h => by
    show z.1 (g * h) - (ρ (g * h) m' - m') = (z.1 g - (ρ g m' - m')) + ρ g (z.1 h - (ρ h m' - m'))
    rw [hz2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hf : (fun g => Lev.mk (w g) (hw g) : G → Lev M c) ∈ Z1 (levRep ρ c) := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val hwlc lev_val_injective).continuous
    · show w (g * h) = w g + ρ g (w h)
      exact hwc g h
  refine ⟨Submodule.Quotient.mk ⟨_, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show levelH1ToModuleH1 ρ c (Submodule.Quotient.mk ⟨_, hf⟩) = Submodule.mkQ _ z
  rw [valuation_H1_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-m', funext fun g => ?_⟩
  show ρ g (-m') - -m' = (z.1 g - (ρ g m' - m')) - z.1 g
  rw [map_neg]
  abel

def preInv (ρ : Representation O G M) (c : O) : Submodule O M :=
  ρ.invariants.comap (c • LinearMap.id : M →ₗ[O] M)

theorem mem_preInv {ρ : Representation O G M} {c : O} (m : M) :
    m ∈ preInv ρ c ↔ ∀ g, ρ g (c • m) = c • m := Iff.rfl

theorem smul_cob_eq_zero {ρ : Representation O G M} {c : O} (m : preInv ρ c) (g : G) :
    c • (ρ g m.1 - m.1) = 0 := by
  rw [smul_sub, ← map_smul (ρ g) c, (mem_preInv _).1 m.2 g, sub_self]

def cobLev (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] Z1 (levRep ρ c) where
  toFun m := ⟨fun g => Lev.mk (ρ g m.1 - m.1) (smul_cob_eq_zero m g), by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val ((hlc m.1).sub (IsLocallyConstant.const m.1))
        lev_val_injective).continuous
    · show ρ (g * h) m.1 - m.1 = (ρ g m.1 - m.1) + ρ g (ρ h m.1 - m.1)
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
  map_add' a b := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (a.1 + b.1) - (a.1 + b.1) = (ρ g a.1 - a.1) + (ρ g b.1 - b.1)
    rw [map_add]; abel))
  map_smul' r a := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (r • a.1) - r • a.1 = r • (ρ g a.1 - a.1)
    rw [map_smul, smul_sub]))

def kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] H1 (levRep ρ c) :=
  (Submodule.mkQ _) ∘ₗ cobLev ρ c hlc

theorem ker_valuation_H1 (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (levelH1ToModuleH1 ρ c) = LinearMap.range (kappa ρ c hlc) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) : H1z ρ) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨m, hm⟩ := h1
    have hm' : ∀ g, ρ g m - m = (f.1 g).val := fun g => congrFun hm g
    have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
      have := congrArg (c • ·) (hm' g)
      simp only [Lev.smul_val, smul_sub] at this
      rw [map_smul, ← sub_eq_zero, ← this]
    refine ⟨⟨m, hP⟩, ?_⟩
    show Submodule.Quotient.mk (cobLev ρ c hlc ⟨m, hP⟩) = Submodule.Quotient.mk f
    congr 1
    exact Subtype.ext (funext fun g => Lev.ext (hm' g))
  · rintro x ⟨m, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c (cobLev ρ c hlc m)) : H1z ρ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m.1, rfl⟩

def toQ (ρ : Representation O G M) (c : O) :
    preInv ρ c →ₗ[O] (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict ρ.invariants
    ((c • LinearMap.id : M →ₗ[O] M) ∘ₗ (preInv ρ c).subtype) (fun m =>
      (Representation.mem_invariants _ _).2 ((mem_preInv _).1 m.2)))

theorem toQ_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m) :
    Function.Surjective (toQ ρ c) := by
  intro y
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := hdiv t.1
  have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
    rw [hm]; exact (Representation.mem_invariants _ _).1 t.2 g
  refine ⟨⟨m, hP⟩, ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext hm

theorem ker_kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (kappa ρ c hlc) = LinearMap.ker (toQ ρ c) := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨ℓ, hℓ⟩ := (mem_coboundaries1 _ _).1 h1
    have hℓ' : ∀ g, ρ g m.1 - m.1 = ρ g ℓ.val - ℓ.val := fun g => congrArg Lev.val (hℓ g)
    have hinv : m.1 - ℓ.val ∈ ρ.invariants := (Representation.mem_invariants _ _).2 fun g => by
      rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp (hℓ' g)
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m.1 - ℓ.val, hinv⟩, Subtype.ext ?_⟩
    show c • (m.1 - ℓ.val) = c • m.1
    rw [smul_sub, Lev.smul_val, sub_zero]
  · intro h
    have h1 : (Submodule.Quotient.mk _ : ρ.invariants ⧸ LinearMap.range
        (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨t, ht⟩ := h1
    have ht' : c • t.1 = c • m.1 := congrArg Subtype.val ht
    have hl : c • (m.1 - t.1) = 0 := by rw [smul_sub, ht', sub_self]
    show (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨Lev.mk (m.1 - t.1) hl, fun g => Lev.ext ?_⟩
    show ρ g m.1 - m.1 = ρ g (m.1 - t.1) - (m.1 - t.1)
    rw [map_sub, (Representation.mem_invariants _ _).1 t.2 g]
    abel

theorem card_H1_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ ϖ n hdiv hlc hfin
  have hdivc := exists_pow_smul_eq hdiv n
  have hs := phi_surjective ρ (ϖ ^ n) hdivc hlc
  refine ⟨Finite.of_surjective _ hs, ?_⟩
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (phi ρ (ϖ ^ n))),
    Nat.card_congr ((phi ρ (ϖ ^ n)).quotKerEquivOfSurjective hs).toEquiv, mul_comm]
  congr 1
  have hker : LinearMap.ker (phi ρ (ϖ ^ n)) = LinearMap.range (kappa ρ (ϖ ^ n) hlc) := by
    rw [phi, LinearMap.ker_codRestrict, LinearMap.ker_codRestrict, ker_valuation_H1]
  rw [hker]
  exact Nat.card_congr (((kappa ρ (ϖ ^ n) hlc).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_kappa ρ (ϖ ^ n) hlc)).trans
      ((toQ ρ (ϖ ^ n)).quotKerEquivOfSurjective (toQ_surjective ρ (ϖ ^ n) hdivc)))).toEquiv)

end GlobalTheory.ShapeNeg.SeqCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardUnramifiedLevelTrivialAction
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def LCHomLev {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (M : Type)
    [AddCommGroup M] [Module O M] (c : O) (I : Subgroup G) : Type :=
  {f : G → Lev M c // IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧ ∀ g ∈ I, f g = 0}

section Triv

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem mem_coboundaries_of_trivial {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m) (x : G → M) :
    x ∈ Formalism.NG.coB1 ρ ↔ x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    funext g
    show ρ g v - v = 0
    rw [hρ, sub_self]
  · rintro rfl
    exact zero_mem _

theorem mk_eq_zero_of_triv {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m)
    (z : Formalism.NG.coZ1s ρ) : (Submodule.Quotient.mk z : Formalism.NG.H1z ρ) = 0 ↔ (z : G → M) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    mem_coboundaries_of_trivial hρ]

variable [TopologicalSpace G]

theorem card_torsion_eq_locConstHom_trivial_action (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m)
    (I : Subgroup G) (c : O) :
    Nat.card (LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (LCHomLev M c I) := by
  have hres : ∀ (g : I) (m : M), Formalism.NG.resRep ρ I g m = m := fun g m => hρ g m
  let coc : LCHomLev M c I → Formalism.NG.coZ1s ρ := fun f =>
    ⟨fun g => (f.1 g).val, fun a b => by
      show (f.1 (a * b)).val = (f.1 a).val + ρ a (f.1 b).val
      rw [hρ, f.2.2.1, Lev.val_add]⟩
  let F : LCHomLev M c I → LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype)) := fun f =>
    ⟨⟨⟨Submodule.Quotient.mk (coc f),
        Submodule.mem_map.2 ⟨coc f, f.2.1.comp Lev.val, rfl⟩⟩,
      by
        change (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I (coc f)) :
          Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0
        rw [mk_eq_zero_of_triv hres]
        funext g
        show (f.1 g.1).val = 0
        rw [f.2.2.2 g.1 g.2]
        rfl⟩,
      by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        apply Subtype.ext
        show c • (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) = 0
        rw [← Submodule.Quotient.mk_smul, mk_eq_zero_of_triv hρ]
        funext g
        exact Lev.smul_val (f.1 g)⟩
  have hinj : ∀ f f' : LCHomLev M c I, (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) =
      Submodule.Quotient.mk (coc f') → f = f' := by
    intro f f' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_of_triv hρ] at h
    apply Subtype.ext
    funext g
    apply Lev.ext
    have h1 : (f.1 g).val - (f'.1 g).val = 0 := congrFun h g
    exact sub_eq_zero.1 h1
  refine (Nat.card_eq_of_bijective F ⟨fun f f' h => hinj f f' ?_, fun y => ?_⟩).symm
  · exact congrArg (fun y => y.1.1.1) h
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.1.1.2
    have hk : (Submodule.Quotient.mk (c • z) : Formalism.NG.H1z ρ) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      change c • Submodule.mkQ _ z = 0
      rw [hzy]
      exact congrArg (fun w => w.1.1) (LinearMap.mem_ker.1 y.2)
    rw [mk_eq_zero_of_triv hρ] at hk
    have hz0 : ∀ g, c • (z : G → M) g = 0 := fun g => congrFun hk g
    have hu : Formalism.NG.resH1 ρ I (Submodule.mkQ _ z) = 0 := by
      rw [hzy]
      exact y.1.2
    have hu' : (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I z) :
        Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0 := hu
    rw [mk_eq_zero_of_triv hres] at hu'
    have hI0 : ∀ g ∈ I, (z : G → M) g = 0 := fun g hg => congrFun hu' ⟨g, hg⟩
    let f : LCHomLev M c I := ⟨fun g => Lev.mk ((z : G → M) g) (hz0 g),
      IsLocallyConstant.desc _ Lev.val hz (fun a b h => Lev.ext h),
      fun a b => Lev.ext (by rw [Lev.val_add, Lev.val_mk, Lev.val_mk, Lev.val_mk, z.2 a b, hρ]),
      fun g hg => Lev.ext (by rw [Lev.val_mk, hI0 g hg]; rfl)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.Quotient.mk (coc f) = y.1.1.1
    rw [← hzy]
    rfl

end Triv

section H1Triv

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {N : Type}
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

theorem H1_mk_eq_zero_iff_of_trivial {rho : Representation R Γ N} (hrho : ∀ g m, rho g m = m)
    (z : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = 0 ↔ z = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    funext g
    rw [hm g, hrho, sub_self]
    rfl
  · rintro rfl
    exact ⟨0, fun g => by rw [map_zero, sub_zero]; rfl⟩

theorem mk_mem_H1ur_of_vanish (rho : Representation R Γ N) (J : Subgroup Γ) (z : Z1 rho)
    (hz : ∀ g ∈ J, z.1 g = 0) : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J := by
  change (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
    H1 (rho.comp J.subtype)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact (mem_coboundaries1 _ _).2 ⟨0, fun g => by rw [map_zero, sub_zero]; exact hz g.1 g.2⟩

theorem vanish_of_mk_mem_H1ur (rho : Representation R Γ N) (J : Subgroup Γ)
    (hJ : ∀ g ∈ J, ∀ m, rho g m = m) (z : Z1 rho)
    (hz : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J) (g : Γ) (hg : g ∈ J) : z.1 g = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
      H1 (rho.comp J.subtype)) = 0 := hz
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  have h3 : z.1 g = rho g m - m := hm ⟨g, hg⟩
  rw [h3, hJ g hg, sub_self]

end H1Triv

theorem card_LCHomLev_eq_unrK {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m) (I : Subgroup G)
    (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) (r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    letI := levZ (M := M) p r h
    Nat.card (LCHomLev M c I) =
      Nat.card (Formalism.GaloisCohomology.unrK (levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  letI := levZ (M := M) p r h
  let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  let F : LCHomLev M c I → Formalism.GaloisCohomology.unrK ρ' := fun f =>
    ⟨Submodule.Quotient.mk ⟨f.1 ∘ i.symm, (f.2.1.comp_continuous i.symm.continuous).continuous,
        fun a b => by
          show f.1 (i.symm (a * b)) = f.1 (i.symm a) + ρ' a (f.1 (i.symm b))
          rw [hρ', map_mul, f.2.2.1]⟩,
      mk_mem_H1ur_of_vanish ρ' _ _ fun g hg => by
        show f.1 (i.symm g) = 0
        exact f.2.2.2 _ ((hI _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg))⟩
  refine Nat.card_eq_of_bijective F ⟨fun f f' hff => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hff
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, H1_mk_eq_zero_iff_of_trivial hρ', sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    funext g
    have h3 := congrFun h2 (i g)
    simpa only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] using h3
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx : (Submodule.Quotient.mk z : H1 ρ') ∈ H1ur ρ' (Formalism.GaloisCohomology.inertiaK p K) := by
      rw [hz]; exact x.2
    let f : LCHomLev M c I := ⟨fun g => z.1 (i g),
      ((IsLocallyConstant.iff_continuous _).2 z.2.1).comp_continuous i.continuous,
      fun a b => by
        show z.1 (i (a * b)) = z.1 (i a) + z.1 (i b)
        rw [map_mul, z.2.2, hρ'],
      fun g hg => vanish_of_mk_mem_H1ur ρ' _ (fun σ _ m => hρ' σ m) z hx (i g) ((hI g).1 hg)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change Submodule.Quotient.mk _ = x.1
    rw [← hz]
    congr 1
    apply Subtype.ext
    funext g
    show z.1 (i (i.symm g)) = z.1 g
    rw [ContinuousMulEquiv.apply_symm_apply]

open scoped ReciprocityTheory.DiscreteGroups.LocalClassField in

theorem card_unramifiedClasses_eq_card_invariants_localGalois {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    (rho : Representation R (Formalism.GaloisCohomology.GK p K) N) (hrho : ReciprocityTheory.Gal.ContAction rho)
    (hI : ∀ σ ∈ Formalism.GaloisCohomology.inertiaK p K, ∀ m, rho σ m = m) :
    Nat.card (Formalism.GaloisCohomology.unrK rho) = Nat.card (H0 rho) := by
  change Nat.card (Neutral.B1.H1ur rho (Neutral.B1.inertiaK p K)) = Nat.card (Neutral.B1.H0 rho)
  replace hI : ∀ σ ∈ Neutral.B1.inertiaK p K, ∀ m, rho σ m = m := hI
  rw [← ReciprocityTheory.DiscreteGroups.LocalClassField.subG_Kur_eq_inertiaK hK] at hI ⊢
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles.card_H1ur hrho hI (s := ReciprocityTheory.DiscreteGroups.LocalClassField.frobK p K)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur hK)

theorem card_unr_lev_of_triv : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {ϖ : O},
    Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O G M), (∀ g m, ρ g m = m) →
    ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) → ∀ n : ℕ,
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro p _ K hK O _ _ _ _ ϖ hϖ hp G _ _ i M _ _ e ρ hρ I hI n
  have hpn : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} :=
    Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hp) n)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI := levZ (M := M) p n hpn
  obtain ⟨hfin, hcard⟩ := levKO_card hϖ e n
  haveI := hfin
  let ρ' := levRepZ p n hpn (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  have hcont : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ']
    exact continuous_snd
  calc _ = Nat.card (LCHomLev M (ϖ ^ n) I) := card_torsion_eq_locConstHom_trivial_action ρ hρ I (ϖ ^ n)
    _ = Nat.card (Formalism.GaloisCohomology.unrK ρ') := card_LCHomLev_eq_unrK i ρ hρ I hI n (ϖ ^ n) hpn
    _ = Nat.card (H0 ρ') :=
        card_unramifiedClasses_eq_card_invariants_localGalois hK ρ' hcont (fun σ _ m => hρ' σ m)
    _ = Nat.card (Lev M (ϖ ^ n)) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x g => hρ' g x)
    _ = _ := hcard

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOneStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l), ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | exact GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | (intros; apply GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_additive_exact_sequence : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  first | exact @GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | exact GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | (intros; apply GlobalTheory.Models.sen_eq_sen_pre_add_sen_push <;> assumption)
end

