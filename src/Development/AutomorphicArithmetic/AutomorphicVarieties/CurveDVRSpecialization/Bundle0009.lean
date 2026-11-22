import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GfResZpow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.WeightZeroAlgebraLeEntryAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open Matrix Formalism.MainNotions.N in
private theorem ss_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

private theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : Af.IsAutCsd ι r) : Af.IsAutCsd ι r' := by
  obtain ⟨π, h1, h2, h3, h4⟩ := H
  refine ⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H

private theorem att_iso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {k : ℕ} {ι : Qbar l ≃+* ℂ}
    {f : Af.Newform k} {r r' : G ℚ Ω →* GL (Fin 2) (Qbar l)} (h : Af.RepIso r r') (H : f.Att ι r) : f.Att ι r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ss_conj g hg H.1, H.2.mono fun w hw A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · rw [hg, (hw A hA).1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A hA).2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private def dg {R : Type} [CommRing R] (t : Rˣ) : GL (Fin 2) R where
  val := Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)]
  inv := Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp

private theorem corner_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G) :
    corner (conjBy (tor R t) r g).mat =
      (dg t : Matrix (Fin 2) (Fin 2) R) * corner (r g).mat * (((dg t)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  ext a b
  show _ = (Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)] * corner (r g).mat *
    Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)] : Matrix (Fin 2) (Fin 2) R) a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
    (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
  congr 1
  · congr 1
    fin_cases a <;> simp [wt1]
  · fin_cases b <;> simp [wt1]

theorem UpperTheory.V.Pr.automorphy_rank_three_of_endomorphisms :
    Loc.LocalPublishedTheorems → GdEnd → AutomorphyUnramifiedCoefficients := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      rw [ht, conj_left r _ _ ((hr s).trans hs)]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') := matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    exact autCsd_iso (tw_iso _ hiso.symm') key
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj (dg t)).toMonoidHom.comp W
    have hW' : ∀ s, W' s = dg t * W s * (dg t)⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, matIrr_conj (dg t) (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [corner_conj]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    obtain ⟨f, hf⟩ := h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, corner_conj, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2])
    exact ⟨f, att_iso (tw_iso _ (Af.RepIso.symm' ⟨dg t, hW'⟩)) hf⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Aut
open scoped Pointwise

namespace UpperTheory.V.Pr

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def upl (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Subgroup (G ℚ Ω) where
  carrier := {s | ∀ x ∈ maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

variable {Ω} {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]

structure GalLink (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)) where
  ab : IsAbelianGalois ℚ L
  gal : galOf ℚ L Ω = upl Ω L ⊓ η.ker
  unr : ∀ B' : ValuationSubring Ω, Ine (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  split : ∀ B' : ValuationSubring Ω, B'.valuation (M : Ω) < 1 → Dec (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  teich : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ upl Ω L,
    barChar O Ψ s = 1 → Ψ s = 1
  p : upl Ω L →* Φ.Γ
  p_cont : Continuous p
  p_surj : Function.Surjective p
  p_ker : p.ker = (Subgroup.normalClosure {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧
    s.1 ∈ Ine (F := ℚ) B' ∧ η s = 1 ∧ barChar O Ψ s = 1}).topologicalClosure
  del : ∀ s, Φ.del (p s) = η s
  eps : ∀ s, Φ.eps (p s) = cycZ ℚ Ω l s
  psi : ∀ s, Φ.Ψ (p s) = barChar O Ψ s
  c : ∃ h : σ ∈ upl Ω L, p ⟨σ, h⟩ = Φ.c
  g0 : ∃ h : g₁ ∈ upl Ω L, p ⟨g₁, h⟩ = Φ.g0
  pl : Φ.V → ValuationSubring Ω
  pl_conj : ∀ v, ∃ γ : G ℚ Ω, η γ = 1 ∧ pl v = γ • B
  pl_all : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃! v, ∃ u ∈ upl Ω L, B' = u • pl v
  j : ∀ v, Φ.Gv v →* upl Ω L
  j_cont : ∀ v, Continuous (j v)
  j_inj : ∀ v, Function.Injective (j v)
  j_range : ∀ v (s : upl Ω L), s ∈ (j v).range ↔ s.1 ∈ Dec (F := ℚ) (pl v)
  j_loc : ∀ v g, Φ.loc v g = p (j v g)
  j_ine : ∀ v g, g ∈ Φ.Iv v ↔ (j v g).1 ∈ Ine (F := ℚ) (pl v)
  dv : ∀ v, Φ.dv v = (upl Ω L).relIndex (Dec (F := ℚ) (pl v))
  mu : ∀ v, ∃ g, cycMod ℚ Ω l 1 (j v g) ≠ 1

def GalLink.p0 {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ)
    (s : G L Ω) : Φ.G0 :=
  have h : galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := k.gal ▸ galEmb_mem ℚ L Ω s
  ⟨k.p ⟨galEmb ℚ L Ω s, h.1⟩, (k.del _).trans h.2⟩

def SeedClause (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (N w : ℕ) (χ' η' θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    Sd.FieldPairCharacterTripleConditions K L σ N w χ' η' θ j ∧ χ' ≠ η' ∧ ¬ l ∣ orderOf χ' ∧ (∀ s, (η' s).val = (((η s).val : ℤ) : Qbar l)) ∧
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Ψ s).val.1‖ < 1) ∧ ¬ (l : ℤ) ∣ discr K

def HasFrame (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω)
    (M : ℕ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω) (g₁ : G ℚ Ω)
    (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ), Nonempty (GalLink η Ψ σ g₁ B M L Φ) ∧ Φ.Ok C₀ ∧ Φ.Big C₀ ∧
      SeedClause c η Ψ σ L

def HostFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l]
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
    HasFrame c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B (l * N)

def GdFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
    HasFrame c D.η D.Ψ D.cc B (l * N * (discr K).natAbs)

end UpperTheory.V.Pr

end
end

