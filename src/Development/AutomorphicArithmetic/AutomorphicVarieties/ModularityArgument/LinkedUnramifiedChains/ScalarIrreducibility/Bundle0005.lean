import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FreeEtaleSheafZmodExistsHomSendingGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FixLe
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.fixLe :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → S.u.TI (RingHom.ker ξ) →
          (∀ D ∈ FixTan S ξ, ∃ X : Matrix (Fin n) (Fin n) (Qbar l), ∀ g, (S.u.r g).map D = X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) →
          Module.rank (Qbar l) (FixTan S ξ) ≤ 1 := by
  intro l _ c _ F C₀ n hF hn S ξ hI hT hX
  have hirr := irrTI l c F C₀ n hF hn S ξ hI hT
  have key : ∀ D ∈ FixTan S ξ, ∃ t : Qbar l,
      (∀ (g : F.G0) (i j : Fin n), D (S.u.r g i j) = t * ↑(Fr.w n i - Fr.w n j) * ξ (S.u.r g i j)) ∧
      ∀ (v : F.V) (i : Fin n) (g : F.Gv v), D ↑((S.u.ψ v i) g) = 0 := by
    intro D hD
    obtain ⟨X, hXD⟩ := hX D hD
    exact torus l c F C₀ n hF hn S ξ hI D hD.1 hirr X hXD
  by_cases h0 : ∀ D ∈ FixTan S ξ, D = 0
  · have hbot : FixTan S ξ = ⊥ := eq_bot_iff.2 fun D hD => (Submodule.mem_bot _).2 (h0 D hD)
    rw [hbot]
    simp
  push_neg at h0
  obtain ⟨D1, hD1, hne⟩ := h0
  obtain ⟨t1, h1r, h1ψ⟩ := key D1 hD1
  have ht1 : t1 ≠ 0 := by
    rintro rfl
    exact hne (derExt l c F C₀ n hF hn S ξ D1 hD1.1 (fun g i j => by simp [h1r]) h1ψ)
  haveI : Module.Free (Qbar l) (FixTan S ξ) := Module.Free.of_divisionRing _ _
  refine (rank_submodule_le_one_iff _).2 ⟨D1, hD1, fun D hD => ?_⟩
  obtain ⟨t, hr, hψ⟩ := key D hD
  have hE : t1 • D - t • D1 = 0 :=
    derExt l c F C₀ n hF hn S ξ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hD.1) (Submodule.smul_mem _ _ hD1.1))
      (fun g i j => by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, h1r]
        ring)
      (fun v i g => by simp [hψ, h1ψ])
  rw [Submodule.mem_span_singleton]
  refine ⟨t1⁻¹ * t, ?_⟩
  rw [mul_smul, ← sub_eq_zero.1 hE, smul_smul, inv_mul_cancel₀ ht1, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th

private def nb (l : ℕ) [Fact l.Prime] : ValuationSubring (Qbar l) where
  carrier := {a | ‖a‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' a := by
    rcases le_total ‖a‖ 1 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      change ‖a⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

private theorem nb_max {l : ℕ} [Fact l.Prime] (x : nb l) : x ∈ maximalIdeal (nb l) ↔ ‖(x : Qbar l)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    refine lt_of_le_of_ne x.2 fun e => h ?_
    have hx : (x : Qbar l) ≠ 0 := fun h0 => by simp [h0] at e
    have hi : (x : Qbar l)⁻¹ ∈ nb l := by
      change ‖(x : Qbar l)⁻¹‖ ≤ 1
      rw [norm_inv, e, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hx))
  · intro h hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 := congrArg (fun t : nb l => ‖(t : Qbar l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h2 : ‖(y : Qbar l)‖ ≤ 1 := y.2
    nlinarith [norm_nonneg (x : Qbar l), norm_nonneg (y : Qbar l)]

private theorem flag_int {l : ℕ} [Fact l.Prime] {H : Type} [Group H] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) (Qbar l))
    (ψ : Fin n → H →* (Qbar l)ˣ) (g₀ : H) (hr : ∀ s i j, ‖r s i j‖ ≤ 1) (hψ : ∀ i s, ‖((ψ i s : (Qbar l)ˣ) : Qbar l)‖ ≤ 1)
    (hu : ∀ i j, i ≠ j → 1 ≤ ‖((ψ i g₀ : (Qbar l)ˣ) : Qbar l) - ψ j g₀‖)
    (hd : ∀ i, ‖r g₀ i i - ψ i g₀‖ < 1) (ho : ∀ i j, i ≠ j → ‖r g₀ i j‖ < 1)
    (hord : ∀ g, Fr.ordProd r (fun i s => ((ψ i s : (Qbar l)ˣ) : Qbar l)) g = 0) : W.HasFlag r.toHomUnits ψ := by
  let j : nb l →+* Qbar l := (nb l).subtype
  have hj : Function.Injective j := Subtype.val_injective
  let rC : H →* Matrix (Fin n) (Fin n) (nb l) :=
    { toFun := fun s => Matrix.of fun a b => ⟨r s a b, hr s a b⟩
      map_one' := by
        refine Matrix.map_injective (f := j) hj ?_
        ext a b
        change r 1 a b = ((1 : Matrix (Fin n) (Fin n) (nb l)).map j) a b
        rw [map_one, Matrix.map_one _ (map_zero j) (map_one j)]
      map_mul' := fun s t => by
        refine Matrix.map_injective (f := j) hj ?_
        have h : ∀ s, (Matrix.of fun a b => (⟨r s a b, hr s a b⟩ : nb l)).map j = r s := fun s => by
          ext a b
          rfl
        refine (h _).trans ?_
        change r (s * t) = j.mapMatrix (_ * _)
        rw [map_mul j.mapMatrix]
        change _ = Matrix.map _ _ * Matrix.map _ _
        rw [h, h, map_mul] }
  have hrC : ∀ s, j.mapMatrix (rC s) = r s := fun s => by
    ext a b
    rfl
  let ψC : Fin n → H →* (nb l)ˣ := fun i =>
    { toFun := fun s => ⟨⟨ψ i s, hψ i s⟩, ⟨ψ i s⁻¹, hψ i s⁻¹⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun s t => by ext; simp }
  have hψC : ∀ i, W.pushCh j (ψC i) = ψ i := fun i => by
    ext s
    rfl
  have hfl : W.HasFlag rC.toHomUnits ψC := by
    refine Fr.flag_loc rC ψC g₀ (fun a b hab => ?_) ?_ fun g => ?_
    · by_contra hn
      have h1 := (nb_max _).1 hn
      exact absurd (hu a b hab) (not_le.2 h1)
    · have hdg : (rC g₀).map (residue (nb l)) = Matrix.diagonal fun i => residue (nb l) (ψC i g₀ : (nb l)ˣ) := by
        ext a b
        by_cases hab : a = b
        · subst hab
          rw [Matrix.diagonal_apply_eq, Matrix.map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, nb_max]
          exact hd a
        · rw [Matrix.diagonal_apply_ne _ hab, Matrix.map_apply, residue_eq_zero_iff, nb_max]
          exact ho a b hab
      rw [hdg, Matrix.charpoly_diagonal]
    · refine Matrix.map_injective (f := j) hj ?_
      change j.mapMatrix _ = j.mapMatrix 0
      rw [← Fr.ordProd_map, map_zero]
      simp only [hrC]
      exact hord g
  obtain ⟨g, hg⟩ := hfl
  have key : ∀ s a b, (Matrix.GeneralLinearGroup.map j g * r.toHomUnits s * (Matrix.GeneralLinearGroup.map j g)⁻¹ :
      GL (Fin n) (Qbar l)) a b = j ((g * rC.toHomUnits s * g⁻¹ : GL (Fin n) (nb l)) a b) := fun s a b => by
    have h1 : r.toHomUnits s = Matrix.GeneralLinearGroup.map j (rC.toHomUnits s) := Units.ext (hrC s).symm
    rw [h1, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨Matrix.GeneralLinearGroup.map j g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩
  · rw [key, (hg s).1 a b hab, map_zero]
  · rw [key, (hg s).2 a]
    rfl

private theorem w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ Fr.w n i ≠ a ^ Fr.w n j := by
  intro h
  have h1 : a ^ (Fr.w n i - Fr.w n j) = 1 := by rw [_root_.zpow_sub, h, mul_inv_cancel]
  have h2 : Fr.w n i - Fr.w n j ∣ 2 := by
    clear h h1
    revert i j
    rcases hn with rfl | rfl <;> decide
  obtain ⟨c, hc⟩ := h2
  apply ha
  have h3 : a ^ (2 : ℤ) = 1 := by rw [hc, _root_.zpow_mul, h1, _root_.one_zpow]
  exact_mod_cast h3

section Pt

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)

private theorem small_of_res (ξ : S.A →ₐ[c.O] Qbar l) (h : IntPt S ξ) (b : S.B) (hb : res c.O S.R (b : S.R) = 0) :
    ‖ξ (S.inc b)‖ < 1 :=
  h.2 b ((res_eq_zero_iff c.O S.R _).1 hb)

private theorem big_of_res (ξ : S.A →ₐ[c.O] Qbar l) (h : IntPt S ξ) (b : S.B) (hb : res c.O S.R (b : S.R) ≠ 0) :
    1 ≤ ‖ξ (S.inc b)‖ := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) (b : S.R)
  have hu : IsUnit a := by
    by_contra hn
    have h1 : algebraMap c.O S.R a ∈ maximalIdeal S.R := fun h' => hn (isUnit_of_map_unit _ _ h')
    exact hb ((res_eq_zero_iff c.O S.R _).2 (by simpa using Ideal.add_mem _ ha h1))
  obtain ⟨a', ha'⟩ := hu.exists_right_inv
  have e : ∀ t : c.O, ξ (algebraMap c.O S.A t) = algebraMap c.O (Qbar l) t := fun t => ξ.commutes t
  have h1 : ‖algebraMap c.O (Qbar l) a‖ = 1 := by
    have h2 : ‖algebraMap c.O (Qbar l) a‖ ≤ 1 := by rw [← e]; exact h.1 _
    have h3 : ‖algebraMap c.O (Qbar l) a'‖ ≤ 1 := by rw [← e]; exact h.1 _
    have h4 : ‖algebraMap c.O (Qbar l) a‖ * ‖algebraMap c.O (Qbar l) a'‖ = 1 := by
      rw [← norm_mul, ← map_mul, ha', map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap c.O (Qbar l) a), norm_nonneg (algebraMap c.O (Qbar l) a')]
  have h5 : ‖ξ (S.inc (b - algebraMap c.O S.B a))‖ < 1 := h.2 _ ha
  rw [map_sub, map_sub, AlgHom.commutes, e] at h5
  by_contra hn
  have h6 := IsUltrametricDist.norm_add_le_max (ξ (S.inc b)) (-(ξ (S.inc b) - algebraMap c.O (Qbar l) a))
  rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel, h1] at h6
  exact absurd h6 (not_le.2 (max_lt (not_le.1 hn) h5))

private theorem pt_flag (ξ : S.A →ₐ[c.O] Qbar l) (hV : VPt S ξ) (hn : n = 2 ∨ n = 3) (v : F.V) (g₀ : F.Gv v)
    (hg : F.Ψ (F.loc v g₀) ^ 2 ≠ 1) :
    W.HasFlag ((ptRep S ξ).r.comp (F.loc0 v)).toHomUnits ((ptRep S ξ).ψ v) := by
  have hb : ∀ i g, res c.O S.R (S.ψB v i g : S.R) = ((F.Ψ (F.loc v g) ^ Fr.w n i : (ResidueField c.O)ˣ) : ResidueField c.O) :=
    fun i g => S.lift.2.1.2 v i g
  have ha : ∀ g i, res c.O S.R (S.aB g i : S.R) = ((F.Ψ g ^ Fr.w n i : (ResidueField c.O)ˣ) : ResidueField c.O) :=
    fun g i => S.lift.2.1.1 g i
  refine flag_int _ _ g₀ (fun s i j => hV.1.1 _) (fun i s => hV.1.1 _) (fun i j hij => ?_) (fun i => ?_) (fun i j hij => hV.2 _ i j hij)
    fun g => (ptRep S ξ).ord v g
  · have h1 := big_of_res S ξ hV.1 (S.ψB v i g₀ - S.ψB v j g₀) (by
      intro h0
      have h2 : res c.O S.R (S.ψB v i g₀ : S.R) = res c.O S.R (S.ψB v j g₀ : S.R) := by
        rw [← sub_eq_zero, ← map_sub]
        exact h0
      rw [hb, hb] at h2
      exact w_ne hn _ hg i j hij (Units.ext h2))
    rw [map_sub, map_sub] at h1
    exact h1
  · have h1 := small_of_res S ξ hV.1 (S.aB (F.loc0 v g₀) i - S.ψB v i g₀) (by
      change res c.O S.R ((S.aB (F.loc0 v g₀) i : S.R) - (S.ψB v i g₀ : S.R)) = 0
      rw [map_sub, hb, ha, sub_eq_zero]
      rfl)
    rw [map_sub, map_sub] at h1
    exact h1

end Pt

private theorem det_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (p : H →* G) (τ : H →* Matrix (Fin n) (Fin n) A)
    (h : ∀ g, τ g = ρ (p g)) : (W.GDet.ofRep ρ).comap p = W.GDet.ofRep τ := by
  refine W.GDet.ext fun C _ _ x => ?_
  change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p x)).det = (W.GDet.repAlg τ C x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, h]

private theorem tw_flag {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
    {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (v : G.Vl)
    (h : W.HasFlag (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (ρ.ψ (K.e v))) :
    W.HasFlag ((K.tw ρ).toHomUnits.comp (G.φ v)) (K.twψ ρ v) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ?_⟩
  have key : ∀ i j, (g * ((K.tw ρ).toHomUnits.comp (G.φ v)) s * g⁻¹ : GL (Fin n) A) i j =
      ((K.κA A (G.φ v s) : Aˣ) : A) *
        (g * (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (K.lam v s) * g⁻¹ : GL (Fin n) A) i j := fun i j => by
    change ((g : Matrix (Fin n) (Fin n) A) * (((K.κA A (G.φ v s) : Aˣ) : A) • ρ.r (K.π (G.φ v s))) *
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j =
      _ * ((g : Matrix (Fin n) (Fin n) A) * ρ.r (F.loc0 (K.e v) (K.lam v s)) *
      ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j
    rw [K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (hg _).1 i j hij, mul_zero]
  · rw [key, (hg _).2 i, mul_comm]
    rfl

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b)
    (ha : A.valuation (a : Ω) < 1) : A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A c))

private theorem unramified_at_base_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {N M : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) (h : l * N ∣ M)
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (M : Ω) < 1) (g : G L Ω) (hg : g ∈ Ine (F := L) A) : k.p0 g = 1 := by
  have hl : ¬ A.valuation (l : Ω) < 1 := fun h' => hA (val_dvd A ((dvd_mul_right l N).trans h) h')
  have hg' : galEmb ℚ L Ω g ∈ Ine (F := ℚ) A := hg
  have h1 : cycZ ℚ Ω l (galEmb ℚ L Ω g) = 1 := (Base.places ℚ Ω l A).2.2.2 hl hg'
  have h2 : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 :=
    (Chr.clsFacts ℚ Ω N).2.2.2.2 A (fun h' => hA (val_dvd A ((dvd_mul_left N l).trans h) h')) hg'
  have h3 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) = 1 := by simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  refine Subtype.ext ?_
  change toUpl Ω L (W.resP L Ω g) ∈ k.p.ker
  rw [k.p_ker]
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hl, hg', ?_, ?_⟩)
  · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
  · exact (congrArg (Units.map (residue O).toMonoidHom) h3).trans (map_one _)

private theorem irr_of_mat {Γ H k : Type} [Group Γ] [Group H] [Field k] {n : ℕ} [NeZero n] (ρ : Γ →* GL (Fin n) k) (p : H →* Γ)
    (hp : Function.Surjective p) (h : MatIrr ⊤ (W.mat ρ)) : Af.IsIrr (ρ.comp p) := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun U _ hU => h U fun g _ v hv => ?_⟩
  obtain ⟨t, rfl⟩ := hp g
  exact hU t v hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.TanBound
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem add_vanish {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] (f : H → PadicAlgCl l) (hf : Continuous f) (hm : ∀ a b, f (a * b) = f a + f b)
    {ι : Type} (u : ι → H) (g : H)
    (hg : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : H →* A, IsOpen (χ.ker : Set H) →
      (∀ a, χ (u a) = 1) → χ g = 1) (hu : ∀ a, f (u a) = 0) : f g = 0 := by
  classical
  have f1 : f 1 = 0 := by
    have h11 := hm 1 1
    rw [mul_one] at h11
    have h12 : f 1 + f 1 = f 1 + 0 := by rw [add_zero, ← h11]
    exact add_left_cancel h12
  have fpow : ∀ (h : H) (m : ℕ), f (h ^ m) = (m : PadicAlgCl l) * f h := by
    intro h m
    induction m with
    | zero => simp [f1]
    | succ m ih =>
      rw [pow_succ, hm, ih]
      push_cast
      ring
  let fm : H →* Multiplicative (PadicAlgCl l) :=
    { toFun := fun h => Multiplicative.ofAdd (f h)
      map_one' := by
        show Multiplicative.ofAdd (f 1) = 1
        rw [f1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (a * b)) = Multiplicative.ofAdd (f a) * Multiplicative.ofAdd (f b)
        rw [hm]
        rfl }
  have hl : ‖((l : ℕ) : PadicAlgCl l)‖ = 1 / (l : ℝ) := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
    simp
  have hl1 : 1 / (l : ℝ) < 1 := by
    have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr h2
  have key : ∀ ε : ℝ, 0 < ε → ‖f g‖ < ε := by
    intro ε hε
    let W : Subgroup (Multiplicative (PadicAlgCl l)) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ < ε}
        one_mem' := by
          show ‖(0 : PadicAlgCl l)‖ < ε
          rw [norm_zero]
          exact hε
        mul_mem' := fun {a b} ha hb => by
          show ‖Multiplicative.toAdd a + Multiplicative.toAdd b‖ < ε
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
        inv_mem' := fun {a} ha => by
          show ‖-Multiplicative.toAdd a‖ < ε
          rw [norm_neg]
          exact ha }
    let N : Subgroup fm.range := W.subgroupOf fm.range
    let χ : H →* fm.range ⧸ N := (QuotientGroup.mk' N).comp fm.rangeRestrict
    have hker : ∀ h, χ h = 1 ↔ ‖f h‖ < ε := by
      intro h
      simp only [χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      rfl
    have hsurj : Function.Surjective χ :=
      (QuotientGroup.mk'_surjective N).comp fm.rangeRestrict_surjective
    have hopen : IsOpen (χ.ker : Set H) := by
      have hset : (χ.ker : Set H) = {h | ‖f h‖ < ε} := by
        ext h
        exact hker h
      rw [hset]
      exact isOpen_lt (continuous_norm.comp hf) continuous_const
    haveI : Finite (fm.range ⧸ N) := by
      haveI : Finite (H ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
      exact Finite.of_surjective (QuotientGroup.kerLift χ)
        (fun a => by
          obtain ⟨h, rfl⟩ := hsurj a
          exact ⟨h, rfl⟩)
    have hp : IsPGroup l (fm.range ⧸ N) := by
      intro a
      obtain ⟨h, rfl⟩ := hsurj a
      have hpos : (0 : ℝ) < ‖f h‖ + 1 := by positivity
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hl1
      refine ⟨k, ?_⟩
      rw [← map_pow, hker, fpow, norm_mul, Nat.cast_pow, norm_pow, hl]
      calc (1 / (l : ℝ)) ^ k * ‖f h‖ ≤ (1 / (l : ℝ)) ^ k * (‖f h‖ + 1) := by
            gcongr
            linarith
        _ < ε / (‖f h‖ + 1) * (‖f h‖ + 1) := by gcongr
        _ = ε := by field_simp
    exact (hker g).mp (hg _ hp χ hopen (fun a => (hker _).mpr (by rw [hu a, norm_zero]; exact hε)))
  by_contra hne
  exact lt_irrefl _ (key _ (norm_pos_iff.mpr hne))

private theorem rank_le_card_add_rank_of_kernel {K M : Type} [Field K] [AddCommGroup M] [Module K M] {ι : Type} [Fintype ι]
    (P Q : Submodule K M) (e : ι → M →ₗ[K] K) (h : ∀ x ∈ P, (∀ i, e i x = 0) → x ∈ Q) :
    Module.rank K P ≤ (Fintype.card ι : ℕ) + Module.rank K Q := by
  classical
  let φ : P →ₗ[K] (ι → K) := LinearMap.pi (fun i => (e i).comp P.subtype)
  have h1 := LinearMap.rank_range_add_rank_ker φ
  have h2 : Module.rank K (LinearMap.range φ) ≤ (Fintype.card ι : ℕ) := by
    calc Module.rank K (LinearMap.range φ) ≤ Module.rank K (ι → K) := Submodule.rank_le _
      _ = _ := rank_fun'
  have h3 : Module.rank K (LinearMap.ker φ) ≤ Module.rank K Q := by
    rw [(Submodule.equivMapOfInjective P.subtype Subtype.val_injective (LinearMap.ker φ)).rank_eq]
    apply Submodule.rank_mono
    rintro _ ⟨x, hx, rfl⟩
    apply h _ x.2
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [φ] using this
  rw [← h1]
  exact add_le_add h2 h3

theorem UpperTheory.V.J.tanBound :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ →
          Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ (n * F.d : ℕ) + Module.rank (Qbar l) (FixTan S ξ) := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  choose u a₀ hu1 hu2 hgen using hF.gen
  let ev : S.A → ((S.A →ₗ[c.O] Qbar l) →ₗ[Qbar l] Qbar l) := fun x =>
    { toFun := fun D => D x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have key := rank_le_card_add_rank_of_kernel (PtDer ξ (Qbar l)) (FixTan S ξ)
    (fun j : (Σ v : F.V, Fin n × Fin (F.dv v)) => ev ↑(S.u.ψ j.1 j.2.1 (u j.1 j.2.2))) ?_
  · have hc : Fintype.card (Σ v : F.V, Fin n × Fin (F.dv v)) = n * F.d := by
      rw [Fintype.card_sigma, UpperTheory.V.Fr.Frame.d, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [hc] at key
    exact key
  · intro D hD hz
    have hD' : ∀ x y, D (x * y) = ξ x • D y + ξ y • D x := hD
    refine Submodule.mem_inf.mpr ⟨hD, ?_⟩
    show ∀ (v : F.V) (i : Fin n), ∀ g ∈ F.Iv v, D ↑((S.u.ψ v i) g) = 0
    intro v i g hg
    obtain ⟨hx, hd⟩ := (derRep l c F C₀ n hF hn S ξ hξ D hD).2.2 v i
    have hne : ∀ h : F.Gv v, ξ ↑((S.u.ψ v i) h) ≠ 0 := by
      intro h hh
      have h1 := congrArg ξ (congrArg Units.val (mul_inv_cancel ((S.u.ψ v i) h)))
      rw [Units.val_mul, map_mul, hh, zero_mul, Units.val_one, map_one] at h1
      exact zero_ne_one h1
    let f : F.Gv v → PadicAlgCl l := fun h => D ↑((S.u.ψ v i) h) * (ξ ↑((S.u.ψ v i) h))⁻¹
    have hfc : Continuous f := hd.mul (hx.inv₀ hne)
    have hfm : ∀ a b, f (a * b) = f a + f b := by
      intro a b
      have ha := hne a
      have hb := hne b
      simp only [f, map_mul, Units.val_mul, hD', smul_eq_mul]
      field_simp
      ring
    have hzero : ∀ a, f (u v a) = 0 := by
      intro a
      have := hz ⟨v, (i, a)⟩
      simp only [f]
      rw [show D ↑((S.u.ψ v i) (u v a)) = 0 from this, zero_mul]
    have h0 := add_vanish f hfc hfm (u v) g
      (fun A _ _ hA χ ho h1 => hgen v A hA χ ho h1 g hg) hzero
    have hg0 := hne g
    simp only [f, mul_eq_zero, inv_eq_zero] at h0
    exact h0.resolve_right hg0
end

