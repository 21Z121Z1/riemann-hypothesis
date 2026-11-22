import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsSumPos
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice
open scoped Classical

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
  {ev : V →ₗ[K] Ω} {D : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : HermLB p}
  {ψ : Ω →+* X.functionField} {s : W → L.B.Sec}

theorem IsModelOf.fs_sum_pos (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) {N n : ℕ} {b : Module.Basis (Fin N) K V}
    {g : Matrix (Fin N) (Fin n) K} {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {c : Matrix (Fin n) (Fin N) K}
    {gw : Fin n → W} (hF : IsFrame Nm W b g A) (hg : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hc : ∀ j, b j = ∑ k, c k j • (gw k : V)) (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K)))
    (hy : y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i)) :
    0 < ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun hS => ?_
  obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
  have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
  have hb := GlobalTheory.frame_semilinear_sq_le K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
    (fun m β u x hx => valR_section_sum K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
  rw [← hS, mul_zero] at hb
  exact hne (by
    have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
    exact norm_eq_zero.1 this)

theorem IsModelOf.fs_shift (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) (t : ℝ) :
    ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame (fun σ x => Real.exp (-t) * Nm σ x) W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧
      (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) →
        ((L.shift (fun _ => t) (fun _ => rfl)).φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  refine ⟨N, n, b, g, fun σ => ((Real.exp t : ℝ) : ℂ) • A σ, c, gw,
    ⟨hF.span, hF.full, fun σ => ?_, fun σ x => ?_, fun σ x => ?_⟩, hg, hc, fun σ i y hy => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')) (hF.herm σ)
  · simp only [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _)]
    rw [hF.conj σ x]
  · rw [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _), hF.norm]
  · have hpos := hM.fs_sum_pos hev hF hg hc σ i y hy
    have e : ∑ a, ‖∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) *
          valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 =
        Real.exp t ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) =
          ((Real.exp t : ℝ) : ℂ) * ∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]; ring
      rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [e, Real.log_mul (pow_pos (Real.exp_pos _) 2).ne' hpos.ne', Real.log_pow, Real.log_exp, ← hφ σ i y]
    change (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y + 2 * t = _
    push_cast
    ring

end GlobalTheory.ImageModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionRootsOfUnity
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem cyclotomic_character_of_ringEquiv : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  intro g k hk
  have hk0 : k ≠ 0 := hk.ne'
  haveI : NeZero k := ⟨hk0⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk0
  have hg : IsPrimitiveRoot (g ζ) k := hprim.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime k := (hprim.pow_iff_coprime hk i).1 (hi ▸ hg)
  refine ⟨(i : ℤ), Nat.isCoprime_iff_coprime.2 hcop, fun n => ?_⟩
  have key : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * m / k) = ζ ^ m := by
    intro m
    rw [hζ, ← Complex.exp_int_mul]
    congr 1
    ring
  calc g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = g (ζ ^ n) := by rw [key n]
    _ = (ζ ^ i) ^ n := by rw [map_zpow₀, hi]
    _ = ζ ^ ((i : ℤ) * n) := by rw [← zpow_natCast, ← zpow_mul]
    _ = _ := by
      rw [← key]
      congr 1
      push_cast
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Finite → IsGal ρ → ∀ (Y X : Scheme.{0}) (p : Y ⟶ Sp R) (p' : X ⟶ Sp R') (β : X ⟶ Y), Flat p → IsPullback β p' p (spMap ρ) → ∀ (act : Gal ρ → (X ⟶ X)), (∀ σ, act σ ≫ p' = p' ≫ spMap (Gal.hom σ)) → (∀ σ, act σ ≫ β = β) → ∀ z₀ z : X, β z₀ = β z → ∃ σ : Gal ρ, act σ z₀ = z := by
  first | exact @GlobalTheory.Mum.GalFibre.exists_act_apply_eq | exact GlobalTheory.Mum.GalFibre.exists_act_apply_eq | (intros; apply GlobalTheory.Mum.GalFibre.exists_act_apply_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisBaseChangeSemiAbelianInvariantUnitsDescendStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  first | exact @GlobalTheory.Mum.InvUnit.invariant_units | exact GlobalTheory.Mum.InvUnit.invariant_units | (intros; apply GlobalTheory.Mum.InvUnit.invariant_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjugateCmPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjWeil

theorem unitOn_spMap (g : ℂ →+* ℂ) (c : ℂˣ) :
    Units.map (spMap g).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map g.toMonoidHom c) := by
  apply Units.ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  exact (congrArg (fun q => q.hom (c : ℂ)) this).symm

theorem diag_lbIso {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {p : X'.A.left ⟶ X.A.left} (hX : X'.IsPullBy X b p) (c : 𝔠.elt) :
    LBIso (X'.diag c) ((X.diag c).pull p) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact LBIso.trans (pull_isLB (X'.isLB c) _) (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (X.isLB c) _) _) hI
    (GlobalTheory.GenSpread.lbIso_pull_pull (X.isLB c) p rfl)

theorem weil_transport : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (g : ℂ ≃+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
      ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
        (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
        ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
          u₀.ex = u'.ex → u₀.IsAH Hm χ →
          ∀ (k : ℕ) (w w' z z' : E), 0 < k → w ∈ lattice c y → w' ∈ lattice c y →
            z ∈ lattice c (y * (upIdele K E t)⁻¹) → z' ∈ lattice c (y * (upIdele K E t)⁻¹) →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z / k) - algebraMap E (Af E) (w / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z' / k) - algebraMap E (Af E) (w' / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            g (Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ) : ℂ) / k)) =
              Complex.exp (-(2 * Real.pi * Complex.I) * ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k) := by
  intro _ _ _ K _ _ t E _ _ _ _ I _ φ g c y _ 𝔠 T X' p hp u' hlat hex u₀ Hm χ hex₀ hAH k w w' z z' hk hw hw' hz hz' hwz hwz'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hL : (T.X.diag T.U.c).IsLB := pull_isLB (T.X.isLB T.U.c) _
  have hL' : (X'.diag T.U.c).IsLB := pull_isLB (X'.isLB T.U.c) _

  obtain ⟨χX, hχX⟩ := T.U.ah
  have mem : ∀ v, v ∈ lattice c y → (fun j ↦ φ (T.U.e j) v) ∈ T.U.u.Λ := fun v hv ↦
    (T.U.lat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divk : ∀ v : E, (fun j ↦ φ (T.U.e j) (v / k)) = (k : ℂ)⁻¹ • fun j ↦ φ (T.U.e j) v := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im : ℝ) : ℂ) / k)) with hc₁
  have H1 := GlobalTheory.T.weil_pairing_torsion_points T.X.A T.X.ab _ hL _ T.U.u _ χX hχX k _ _ c₁ hk (mem w hw) (mem w' hw') rfl
  rw [← divk, ← divk] at H1

  let T₁ : Over (Sp ℂ) := Over.mk (𝟙 (Sp ℂ) ≫ spMap (g : ℂ →+* ℂ))
  let h : T₁ ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk (spMap (g : ℂ →+* ℂ)) (by simp [T₁])
  have H2 := GlobalTheory.CommPairing.weilIs_pull globalFns_holds T.X.ab hL h H1
  rw [show h.left = spMap (g : ℂ →+* ℂ) from rfl, unitOn_spMap] at H2

  have H3 := (GlobalTheory.weilIs_baseChange_of_comm (Sp ℂ) (Sp ℂ) T.X.A X'.A (spMap (g : ℂ →+* ℂ)) p hp.grp _ _ hL hL'
    (diag_lbIso hp T.U.c) ℂ (𝟙 (Sp ℂ)) k (u'.ex (fun j ↦ g (φ (T.U.e j) (z / k))))
    (u'.ex (fun j ↦ g (φ (T.U.e j) (z' / k)))) _ _ _ (hex _ _ hwz).symm (hex _ _ hwz').symm).2 H2

  have memg : ∀ v, v ∈ lattice c (y * (upIdele K E t)⁻¹) → (fun j ↦ g (φ (T.U.e j) v)) ∈ u₀.Λ := by
    intro v hv
    rw [← u₀.ker, hex₀, u'.ker]
    exact (hlat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divg : ∀ v : E, (fun j ↦ g (φ (T.U.e j) (v / k))) = (k : ℂ)⁻¹ • fun j ↦ g (φ (T.U.e j) v) := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k)) with hc₂
  have H4 := GlobalTheory.T.weil_pairing_torsion_points X'.A X'.ab _ hL' _ u₀ Hm χ hAH k _ _ c₂ hk (memg z hz) (memg z' hz') rfl
  rw [hex₀, ← divg, ← divg] at H4
  have e := congrArg Units.val (GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) X'.A _ hL' ℂ (𝟙 (Sp ℂ)) k _ _ _ _ H4 H3)
  simp only [hc₁, hc₂, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe] at e
  have hs : ((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im = ∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, Complex.im_sum]
    rw [← Equiv.sum_comp T.U.e]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hs] at e
  exact e.symm

end GlobalTheory.ConjWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_opens_preimage_le_of_isClosedMap {F Y : Scheme.{0}} (φ : F ⟶ Y) (hφ : IsClosedMap φ) (y : Y)
    (T : F.Opens) (hT : ∀ p, φ p = y → p ∈ T) : ∃ N : Y.Opens, y ∈ N ∧ φ ⁻¹ᵁ N ≤ T := by
  refine ⟨⟨(φ '' (T : Set F)ᶜ)ᶜ, (hφ _ T.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, e⟩
    exact hp (hT p e)
  · intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩

theorem exists_basicOpen_le_of_finite {A : Type} [CommRing A] (s : Set (PrimeSpectrum A)) (hs : s.Finite)
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ b : A, s ⊆ PrimeSpectrum.basicOpen b ∧ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  by_cases hne : s = ∅
  · subst hne
    exact ⟨0, by simp, by simp⟩
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  have key : ¬ ((I : Set A) ⊆ ⋃ i ∈ s, (i.asIdeal : Set A)) := by
    rw [Ideal.subset_union_prime_finite hs a a (fun i _ _ _ => i.2)]
    rintro ⟨i, hi, hle⟩
    have : i ∈ Uᶜ := by rw [hI]; exact hle
    exact this (hsU hi)
  obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 key
  refine ⟨b, fun i hi h => hb' (Set.mem_iUnion₂.2 ⟨i, hi, h⟩), fun i hi => ?_⟩
  by_contra h
  have : i ∈ PrimeSpectrum.zeroLocus (I : Set A) := hI ▸ h
  exact hi (this hb)

theorem exists_basicOpen_le_of_finite' {G : Scheme.{0}} {W : G.Opens} (hW : IsAffineOpen W) (s : Set G) (hs : s.Finite)
    (hsW : s ⊆ W) (U : G.Opens) (hsU : s ⊆ U) : ∃ b : Γ(G, W), s ⊆ G.basicOpen b ∧ G.basicOpen b ≤ U := by
  obtain ⟨b, h₁, h₂⟩ := exists_basicOpen_le_of_finite (A := Γ(G, W)) (hW.fromSpec ⁻¹' s)
    (hs.preimage hW.fromSpec.isOpenEmbedding.injective.injOn) _
    (hW.fromSpec ⁻¹ᵁ U).2 (fun p hp => hsU hp)
  refine ⟨b, fun p hp => ?_, ?_⟩
  · have : p ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hsW hp
    obtain ⟨q, rfl⟩ := this
    rw [← hW.fromSpec_image_basicOpen]
    exact ⟨q, h₁ hp, rfl⟩
  · rw [← hW.fromSpec_image_basicOpen]
    rintro _ ⟨q, hq, rfl⟩
    exact h₂ hq

theorem exists_affine_preimage_eq_basicOpen {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {W : G.Opens} (hW : IsAffineOpen W) (y : Y) (hfin : (κ '' {p | φ p = y}).Finite)
    (hy : ∀ p, φ p = y → κ p ∈ W) :
    ∃ (O : Y.Opens) (b : Γ(G, W)), y ∈ O ∧ IsAffineOpen O ∧ φ ⁻¹ᵁ O = κ ⁻¹ᵁ G.basicOpen b := by
  obtain ⟨N, hyN, hN⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ W) hy
  obtain ⟨_, ⟨O₁, hO₁, rfl⟩, hyO₁, hO₁N⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyN N.2
  let U : G.Opens := ⟨(κ '' ((φ ⁻¹ᵁ O₁ : F.Opens) : Set F)ᶜ)ᶜ,
    (κ.isClosedEmbedding.isClosedMap _ (φ ⁻¹ᵁ O₁).2.isClosed_compl).isOpen_compl⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_basicOpen_le_of_finite' hW _ hfin (by rintro _ ⟨p, hp, rfl⟩; exact hy p hp) U (by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
    obtain rfl := κ.isClosedEmbedding.injective e
    apply hq
    change φ q ∈ O₁
    rw [hp]; exact hyO₁)
  have hle : κ ⁻¹ᵁ G.basicOpen b₁ ≤ φ ⁻¹ᵁ O₁ := fun p hp => by
    by_contra h
    exact hb₁' hp ⟨p, h, rfl⟩
  obtain ⟨N₂, hyN₂, hN₂⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ G.basicOpen b₁)
    (fun p hp => hb₁ ⟨p, hp, rfl⟩)
  obtain ⟨g, hg, hyg⟩ := IsAffineOpen.exists_basicOpen_le hO₁ (V := N₂) ⟨y, hyN₂⟩ hyO₁
  have hS : IsAffineOpen (κ ⁻¹ᵁ W) := hW.preimage κ
  rw [Scheme.preimage_basicOpen] at hle hN₂
  obtain ⟨s, hs⟩ := hS.basicOpen_basicOpen_is_basicOpen (κ.app W b₁) (φ.appLE O₁ _ hle g)
  obtain ⟨b, rfl⟩ := κ.app_surjective W hW s
  refine ⟨Y.basicOpen g, b, hyg, hO₁.basicOpen g, ?_⟩
  rw [Scheme.preimage_basicOpen κ, hs, Scheme.basicOpen_appLE, eq_comm, inf_eq_right]
  exact fun p hp => hN₂ (hg hp)

theorem exists_affine_preimage_iff_not_mem {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {A : Type} [CommRing A] (J : Sp A ⟶ G) [IsOpenImmersion J] (y : Y)
    (hfin : (κ '' {p | φ p = y}).Finite) (hy : ∀ p, φ p = y → κ p ∈ Set.range J) :
    ∃ (O : Y.Opens) (b : A), y ∈ O ∧ IsAffineOpen O ∧
      ∀ p, φ p ∈ O ↔ ∃ q : PrimeSpectrum A, J q = κ p ∧ b ∉ q.asIdeal := by
  obtain ⟨O, b, h₁, h₂, h₃⟩ := exists_affine_preimage_eq_basicOpen κ φ hφ (isAffineOpen_opensRange J) y hfin hy
  have e : (⊤ : (Sp A).Opens) ≤ J ⁻¹ᵁ J.opensRange := fun q _ => ⟨q, rfl⟩
  refine ⟨O, (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b), h₁, h₂, fun p => ?_⟩
  have h₄ := basicOpen_eq_of_affine' (R := .of A) (J.appLE _ _ e b)
  rw [Scheme.basicOpen_appLE, top_inf_eq] at h₄
  have h₅ : ∀ q : PrimeSpectrum A, J q ∈ G.basicOpen b ↔
      (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b) ∉ q.asIdeal := fun q => by
    change q ∈ J ⁻¹ᵁ G.basicOpen b ↔ _
    rw [h₄]; rfl
  change p ∈ φ ⁻¹ᵁ O ↔ _
  rw [h₃]
  change κ p ∈ G.basicOpen b ↔ _
  constructor
  · intro h
    obtain ⟨q, hq⟩ := G.basicOpen_le b h
    exact ⟨q, hq, (h₅ q).1 (by rw [hq]; exact h)⟩
  · rintro ⟨q, hq, h⟩
    rw [← hq]; exact (h₅ q).2 h

theorem exists_act_eq_of_apply_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (hG : IsGal (algebraMap R R')) {F G T : Scheme.{0}} (t : T ⟶ Sp R')
    [IsClosedImmersion t] (κ : F ⟶ G) (gm : G ⟶ Sp R') (s : F ⟶ T) (hs : κ ≫ gm = s ≫ t)
    (act : Gal (algebraMap R R') → (G ⟶ G)) (hact : ∀ σ, act σ ≫ gm = gm ≫ spMap (Gal.hom σ)) (Y : Over (Sp R))
    (hY : Flat Y.hom) (φ : F ⟶ Y.left) (hφ : IsPullback φ s Y.hom (t ≫ spMap (algebraMap R R')))
    (hinv : ∀ σ, ∃ h : F ⟶ F, h ≫ κ = κ ≫ act σ ∧ h ≫ φ = φ) (p q : F) (e : φ p = φ q) :
    ∃ σ, act σ (κ p) = κ q := by
  let u : F ⟶ pullback Y.hom (spMap (algebraMap R R')) := pullback.lift φ (s ≫ t) (by rw [hφ.w, Category.assoc])
  have hu₁ : u ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd _ _ = s ≫ t := pullback.lift_snd _ _ _
  have hu : IsPullback s u t (pullback.snd Y.hom (spMap (algebraMap R R'))) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) ?_ hu₂.symm (IsPullback.of_hasPullback _ _).flip
    rw [hu₁]; exact hφ.flip
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hu inferInstance
  obtain ⟨σ, h, h₁, h₂, h₃⟩ := GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange R R' hinj hG Y hY _ _ _ (IsPullback.of_hasPullback _ _) (u p) (u q) (by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hu₁, e])
  obtain ⟨k, k₁, k₂⟩ := hinv σ
  have hk : k ≫ u = u ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, hu₁, k₂]
    · rw [Category.assoc, Category.assoc, h₂, hu₂, ← Category.assoc u, hu₂, ← hs, ← Category.assoc k, k₁, Category.assoc,
        hact, Category.assoc]
  have hkp : k p = q := u.isClosedEmbedding.injective (by
    rw [← h₃, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk])
  exact ⟨σ, by rw [← hkp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, k₁]⟩

theorem mem_range_thick_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R')
    (hρ : ρ.Finite) (P : Sp R') (hP : spMap ρ P = closedPoint R) (e : ℕ) :
    P ∈ Set.range (thick R' (maximalIdeal R') e) := by
  have h₁ : (P.asIdeal.comap ρ).IsMaximal := by
    have : P.asIdeal.comap ρ = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hP
    rw [this]; infer_instance
  have := P.2
  have h₂ : P.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ h₁
  have h₃ : P.asIdeal = maximalIdeal R' := eq_maximalIdeal h₂
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R' ^ (e + 1))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  intro a ha
  change a ∈ P.asIdeal
  rw [h₃]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e) ha

theorem exists_affine_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  intro R _ _ _ R' _ _ _ _ hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec Y φ hY hφ _ hh x hx
  have := hG.1
  have := Fintype.ofFinite (Gal (algebraMap R R'))
  have hx₀ : H.ι x ∈ Set.range (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := by
    rw [Scheme.Pullback.range_fst]
    exact mem_range_thick_of_finite _ hF.2.2 _ hx 0
  obtain ⟨x₀, hx₀⟩ := hx₀
  have ht : IsClosedImmersion (thick R' (maximalIdeal R') 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hρ : IsFinite (spMap (algebraMap R R')) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hfin : IsFinite (φ 0) := MorphismProperty.of_isPullback (P := @IsFinite) (hφ 0).flip inferInstance
  have orb := exists_act_eq_of_apply_eq hF.2.1 hG (thick R' (maximalIdeal R') 0)
    (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) G'.hom _ pullback.condition act hact Y inferInstance (φ 0) (hφ 0) (hh 0)
  have hh₀ := hh 0
  have hκ : IsClosedImmersion (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := inferInstance
  generalize pullback.fst G'.hom (thick R' (maximalIdeal R') 0) = κ at *
  obtain ⟨_, ⟨V₁, hV₁, rfl⟩, hxV₁, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlr, hpb, -, -, hcomm, -, hC⟩ :=
    GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants R R' hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec V₁ hV₁
  have lift : ∀ (z : H.toScheme) (w : Sp C), π z = l w → ∃ q : Sp C', j q = z ∧ spMap (algebraMap C C') q = w :=
    fun z w e => Scheme.exists_preimage_of_isPullback hpb z w e
  have hw : ∀ q, π (j q) = l (spMap (algebraMap C C') q) := fun q => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have hc : ∀ σ q, (j ≫ H.ι) (spMap (actC σ : C' →+* C') q) = act σ ((j ≫ H.ι) q) := fun σ q => by
    rw [← Scheme.Hom.comp_apply, hcomm, ← Scheme.Hom.comp_apply, Category.assoc]
  obtain ⟨w₀, hw₀⟩ : π x ∈ Set.range l := by rw [hlr]; exact hxV₁
  obtain ⟨q₀, hq₀, -⟩ := lift x w₀ hw₀.symm
  have hq₀' : (j ≫ H.ι) q₀ = κ x₀ := by rw [Scheme.Hom.comp_apply, hq₀, hx₀]
  obtain ⟨O, b, hyO, hO, hb⟩ := exists_affine_preimage_iff_not_mem κ (φ 0) (φ 0).isClosedMap (j ≫ H.ι) (φ 0 x₀)
    ((Set.finite_range fun σ => act σ (κ x₀)).subset (by
      rintro _ ⟨p, hp, rfl⟩
      exact orb x₀ p hp.symm))
    (fun p hp => by
      obtain ⟨σ, hσ⟩ := orb x₀ p hp.symm
      exact ⟨_, (hc σ q₀).trans (by rw [hq₀', hσ])⟩)
  let c : C := ⟨∏ σ, actC σ b, (hC _).2 fun τ => by
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => by simp⟩
  have key : ∀ p, φ 0 p ∈ O ↔ ∃ q : PrimeSpectrum C', (j ≫ H.ι) q = κ p ∧ (c : C') ∉ q.asIdeal := fun p => by
    constructor
    · intro hp
      obtain ⟨q, hq, -⟩ := (hb p).1 hp
      refine ⟨q, hq, fun hm => ?_⟩
      obtain ⟨σ, -, hσ⟩ := (q.2.prod_mem_iff).1 hm
      obtain ⟨k, k₁, k₂⟩ := hh₀ σ
      obtain ⟨q', hq', hb'⟩ := (hb (k p)).1 (by rw [← Scheme.Hom.comp_apply, k₂]; exact hp)
      have : q' = spMap (actC σ : C' →+* C') q := (j ≫ H.ι).isOpenEmbedding.injective
        ((hq'.trans (by rw [hq, ← Scheme.Hom.comp_apply k κ, k₁, Scheme.Hom.comp_apply])).trans (hc σ q).symm)
      rw [this] at hb'
      exact hb' hσ
    · rintro ⟨q, hq, hm⟩
      refine (hb p).2 ⟨q, hq, fun hm' => hm ?_⟩
      exact (q.2.prod_mem_iff).2 ⟨1, Finset.mem_univ _, by simpa using hm'⟩
  have key₂ : ∀ z : H.toScheme, π z ∈ l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens) ↔
      ∃ q : PrimeSpectrum C', j q = z ∧ (c : C') ∉ q.asIdeal := fun z => by
    constructor
    · rintro ⟨w, hw', e⟩
      obtain ⟨q, hq, rfl⟩ := lift z w e.symm
      exact ⟨q, hq, hw'⟩
    · rintro ⟨q, rfl, hq⟩
      exact ⟨_, hq, (hw q).symm⟩
  refine ⟨l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens), O, ?_, ?_, hO, ?_⟩
  · obtain ⟨q, hq, hm⟩ := (key x₀).1 hyO
    refine (key₂ x).2 ⟨q, H.ι.isOpenEmbedding.injective ?_, hm⟩
    rw [← hx₀, ← hq]; exact (Scheme.Hom.comp_apply _ _ _).symm
  · refine IsAffineOpen.image_of_isOpenImmersion ?_ l
    rw [← basicOpen_eq_of_affine (R := .of C)]
    exact (isAffineOpen_top _).basicOpen _
  · ext p
    refine (key p).trans ⟨?_, ?_⟩
    · rintro ⟨q, hq, hm⟩
      exact ⟨j q, (key₂ _).2 ⟨q, rfl, hm⟩, hq⟩
    · rintro ⟨z, hz, e⟩
      obtain ⟨q, rfl, hm⟩ := (key₂ z).1 hz
      exact ⟨q, e, hm⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClausesStatement
section
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  first | exact @GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | exact GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | (intros; apply GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor <;> assumption)
end

