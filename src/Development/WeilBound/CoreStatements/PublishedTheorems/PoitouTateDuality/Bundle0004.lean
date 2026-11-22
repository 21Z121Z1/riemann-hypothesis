import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Roots

variable {L : Type} [Field L] {N : ℕ} [NeZero N] (w : rootsOfUnity N L)

theorem rootsOfUnity_pow_N : w ^ N = 1 := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity N (w : Lˣ)).1 w.2

def rootOf : ZMod N →+ Additive (rootsOfUnity N L) where
  toFun c := Additive.ofMul (w ^ c.val)
  map_zero' := by simp
  map_add' a b := by
    show Additive.ofMul (w ^ (a + b).val) = Additive.ofMul (w ^ a.val) + Additive.ofMul (w ^ b.val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, rootsOfUnity_pow_N w,
      one_pow, mul_one]

theorem rootOf_apply (c : ZMod N) : rootOf w c = Additive.ofMul (w ^ c.val) := rfl

theorem rootOf_bijective (hw : IsPrimitiveRoot (((w : Lˣ) : L)) N) : Function.Bijective (rootOf w) := by
  have hwu : IsPrimitiveRoot w N := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
    exact hw
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · have h' : w ^ a.val = w ^ b.val := Additive.ofMul.injective h
    exact ZMod.val_injective N (hwu.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')
  · obtain ⟨i, hi, hx⟩ := hw.eq_pow_of_pow_eq_one
      (ξ := (((Additive.toMul x : rootsOfUnity N L) : Lˣ) : L)) (by
        have := (mem_rootsOfUnity N _).1 (Additive.toMul x).2
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one])
    refine ⟨(i : ZMod N), ?_⟩
    rw [rootOf_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have : w ^ i = Additive.toMul x :=
      Subtype.ext (Units.ext (by rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]; exact hx))
    rw [this]
    rfl

end Roots

section DualGen

variable {Γ H : Type} [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H] (θ : Γ ≃ₜ* H)
  {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module (ZMod N) M] (ρ : Representation (ZMod N) Γ M)
  (χ : Γ →* (ZMod N)ˣ) (A D : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
  (hM : ∀ g m, eM (ρ g m) = A.ρ (θ g) (eM m)) (rr : ZMod N ≃+ D.V)
  (hr : ∀ g c, D.ρ (θ g) (rr c) = rr ((χ g : ZMod N) * c))

include hM hr in

theorem dualGen : ∃ eD : TDual (ZMod N) M ≃+ (dualRep D A).V,
    (∀ g f, eD (twDual χ ρ g f) = (dualRep D A).ρ (θ g) (eD f)) ∧
      ∀ f m, (eD f : A.V →ₗ[ULift.{0} ℤ] D.V) (eM m) = rr (f m) := by
  let fwd : TDual (ZMod N) M → (A.V →ₗ[ULift.{0} ℤ] D.V) := fun f =>
    (uliftIntLinearEquivAddHom A.V D.V).symm
      (rr.toAddMonoidHom.comp (((f : M →ₗ[ZMod N] ZMod N)).toAddMonoidHom.comp eM.symm.toAddMonoidHom))
  let bwd : (A.V →ₗ[ULift.{0} ℤ] D.V) → TDual (ZMod N) M := fun φ =>
    (rr.symm.toAddMonoidHom.comp ((uliftIntLinearEquivAddHom A.V D.V φ).comp eM.toAddMonoidHom)).toZModLinearMap N
  let eD : TDual (ZMod N) M ≃+ (dualRep D A).V :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun f => LinearMap.ext fun m => by
        show rr.symm (rr (f (eM.symm (eM m)))) = f m
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      right_inv := fun φ => LinearMap.ext fun a => by
        show rr (rr.symm (φ (eM (eM.symm a)))) = φ a
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      map_add' := fun f f' => LinearMap.ext fun a => by
        show rr ((f + f') (eM.symm a)) = rr (f (eM.symm a)) + rr (f' (eM.symm a))
        rw [← map_add]
        rfl }
  refine ⟨eD, fun g f => ?_, fun f m => ?_⟩
  · refine LinearMap.ext fun a => ?_
    have h1 : eM.symm (A.ρ (θ g⁻¹) a) = ρ g⁻¹ (eM.symm a) := by
      apply eM.injective
      rw [AddEquiv.apply_symm_apply, hM, AddEquiv.apply_symm_apply]
    show rr ((twDual χ ρ g f) (eM.symm a)) = D.ρ (θ g) (rr (f (eM.symm (A.ρ (θ g)⁻¹ a))))
    rw [hr, ← map_inv, h1]
    rfl
  · show rr (f (eM.symm (eM m))) = rr (f m)
    rw [AddEquiv.symm_apply_apply]

end DualGen

theorem exists_root_of_primitive {L : Type} [Field L] {N : ℕ} (hN0 : N ≠ 0) {z : L}
    (hz : IsPrimitiveRoot z N) : ∃ w : rootsOfUnity N L, ((w : Lˣ) : L) = z :=
  ⟨⟨(hz.isUnit hN0).unit, (mem_rootsOfUnity _ _).2 (Units.ext (by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz.pow_eq_one, Units.val_one]))⟩,
    IsUnit.unit_spec _⟩

set_option maxHeartbeats 1000000 in

theorem gsRoots_act_rootOf (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] [NeZero (l ^ r)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    (hwv : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ)
    (g : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (c : ZMod (l ^ r)) :
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ (e g) (rootOf w c) =
      rootOf w (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := by
  induction g using QuotientGroup.induction_on with
  | H τ =>
  have hm : μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) =
      cycMod Kf.1 (AlgebraicClosure ℚ) l r τ := DFunLike.congr_fun hμ τ
  have hτ : τ ζ = ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val :=
    cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
      (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) τ) ζ hζ.pow_eq_one
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  show (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)) (rootOf w c) =
    rootOf w (((μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) :
      (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c)
  rw [hm]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)
      ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ((((w ^ (((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c).val :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ)
  rw [he τ, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv,
    SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv, map_pow, hτ,
    ← pow_mul, ZMod.val_mul, hmod]

theorem natCast_pow_not_mem (Kf : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hS : ContainsAbove S l) :
    ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 Kf.1))), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∉ v.asIdeal := by
  intro v hv h
  apply hv
  have : ((l : ℕ) : 𝓞 Kf.1) ^ r ∈ v.asIdeal := by simpa using h
  exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r this))

set_option maxHeartbeats 1000000 in
theorem dualCmp' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (hS : ContainsAbove S l)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (A : Rep.{0} (ULift.{0} ℤ)
      (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) :
    ∃ eD : TDual (ZMod (l ^ r)) M ≃+
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V,
      (∀ g f, eD (twDual μ ρ g f) =
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)) ∧
      ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
            (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
            maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
              AlgebraicClosure ℚ) = ζ ^ (f m).val := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) :=
    mem_maxUnramifiedOutside_of_pow_eq_one _ hN0 (natCast_pow_not_mem Kf S hS) hζ.pow_eq_one
  haveI : NeZero (l ^ r) := ⟨hN0⟩
  have hζL : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (l ^ r) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hex := exists_root_of_primitive (L := maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) hN0 hζL
  refine Exists.elim hex (fun w hwv => ?_)
  have hwv' : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ := congrArg Subtype.val hwv
  have hw : IsPrimitiveRoot (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) (l ^ r) := by
    rw [hwv]
    exact hζL
  let rr : ZMod (l ^ r) ≃+ (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).V :=
    AddEquiv.ofBijective (rootOf w) (rootOf_bijective w hw)
  have hrr : ∀ c, rr c = rootOf w c := fun _ => rfl
  have hr : ∀ g c, (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e g) (rr c) = rr (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := fun g c => by
    rw [hrr, hrr]
    exact gsRoots_act_rootOf Kf S ζ hζ e he μ hμ w hwv' g c
  refine Exists.elim (dualGen e ρ μ A
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) eM hM rr hr) (fun eD h => ?_)
  refine ⟨eD, h.1, fun f m => ?_⟩
  rw [h.2, hrr, rootOf_apply]
  show ((((w ^ (f m).val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ζ ^ (f m).val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv']

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

def PerfectQZ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] : Prop :=
  Finite X ∧ Finite Y ∧ ∃ P : X →+ Y →+ QZ, Function.Bijective P ∧ Function.Bijective P.flip

theorem perfectQZ_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (h : PerfectQZ X Y) :
    PerfectQZ Y X := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have e : P.flip.flip = P := by ext; rfl
  exact ⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩

theorem perfectQZ_of_addEquiv {X Y X' Y' : Type} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (eX : X ≃+ X') (eY : Y ≃+ Y') (h : PerfectQZ X' Y') :
    PerfectQZ X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  have bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  refine ⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv,
    (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) =
        (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX := by
      funext x; ext y; rfl
    rw [e]
    exact bY.comp (h1.comp eX.bijective)
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip =
        (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY := by
      funext y; ext x; rfl
    rw [e]
    exact bX.comp (h2.comp eY.bijective)

theorem perfectPair_of_perfectQZ {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectQZ X Y) :
    PerfectPair (R := ZMod n) X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have torX : ∀ x : X, n • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have torY : ∀ y : Y, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hP : ∀ x y, n • P x y = 0 := fun x y => by rw [← map_nsmul, torY, map_zero]
  let Q : X →+ (Y →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n
      map_zero' := by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ]
      map_add' := fun x x' => by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ] }
  have hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y := fun x y =>
    zmodToQZ_zmodOfQZ (P x) (hP x) y
  refine ⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩,
    ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩
  · ext y; rw [← hQ, ← hQ, hxx]
  · obtain ⟨x, hx⟩ := h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩
    rw [hQ, hx]; rfl
  · ext x
    have := congrArg (fun f => zmodToQZ n (f x)) hyy
    exact (hQ x y).symm.trans (this.trans (hQ x y'))
  · obtain ⟨y, hy⟩ := h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩
    show zmodToQZ n (Q.toZModLinearMap n x y) = _
    rw [hQ]
    exact DFunLike.congr_fun hy x

def ShaDictFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) ∧
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2))

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem perfectQZ_of_found {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (h : ∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Y ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (X ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) : PerfectQZ X Y := by
  obtain ⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := poitouTate_sha_gs S' ιs hS hK A hA
  exact perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)

end FoundSide

set_option maxHeartbeats 1000000 in
theorem shaCmpFS_of_dict (h : ShaDictFS) : ShaCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hh := h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1),
    perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 ρ (locFam S Av) (continuous_locFam S Av)) hh.2)⟩

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH1_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH1 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
      refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
      have e := hm (χ g)
      simp only [Submodule.coe_subtype] at e ⊢
      change z.1 (ψ (χ g)) = rho (ψ (χ g)) m - m at e
      rw [h1] at e
      exact e
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨z.1 ∘ χ, z.2.1.comp hχ, fun g h => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h)
        simp only [Function.comp_apply, map_mul]
        rw [e]
        change z.1 (χ g) + rho (ψ (χ g)) (z.1 (χ h)) = _
        rw [h1]
      · rw [resH1, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext h
        change z.1 (χ (ψ h)) = z.1 h
        rw [h2]

theorem resCmp1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      ∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)

end PositivityTheory.Lit1.PTN
end
end

