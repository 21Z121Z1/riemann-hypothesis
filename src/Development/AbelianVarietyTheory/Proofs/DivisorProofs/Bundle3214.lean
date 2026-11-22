import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClass
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.CellDens

theorem dens_smul {n : ℕ} (c : ℂ) (β : Alt n) : dens (c • β) = c * dens β := by
  simp [dens, mul_div_assoc]

theorem dens_blocks (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ)
    (K : T → Fin n → Fin n → ℂ) (r : T → ℕ) (hr : ∀ t, r t = Fintype.card {j // lev j = t})
    (hK : ∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0)
    (α : Alt d) :
    dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, (kappa * K t a b) • sym (a, b)) ^ r t : Ev n) : Alt n)) =
      dens α * ∏ t, ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) := by
  rw [GlobalTheory.T.topDegreeDensity_blockTriangular_diagonalBlocks n d J T ε lev ρ (fun t a b => kappa * K t a b) r hr
    (fun t j h1 h2 b => by simp [(hK t j h1 h2 b).1, (hK t j h1 h2 b).2]) α]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 (t : T) : (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t},
      (kappa * K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1)) : Ev n) ^ r t =
      ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) •
        ∏ a : {j // lev j = t}, (Complex.I / 2) • sym (ε.symm (.inr a.1), ε.symm (.inr a.1)) := by
    have h := GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod n {j // lev j = t} (fun a => ε.symm (.inr a.1))
      (fun a b hab => Subtype.ext (Sum.inr_injective (ε.symm.injective hab)))
      (kappa • Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)))
    rw [Matrix.det_smul, ← hr t] at h
    refine Eq.trans h ?_
    rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, ← hr t, smul_smul]
    congr 1
    have hk : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
      rw [kappa]; field_simp
    rw [hk, mul_pow, inv_pow]
    ring
  simp only [h1]
  rw [Finset.prod_smul, Fintype.prod_fiberwise lev
    (fun j => (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j))), Subalgebra.coe_smul, mul_smul_comm, dens_smul,
    GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume n d J ε α, mul_comm]

theorem cellPot_add {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m)
    (j : Cell m) (h1 : j.root ≠ x) (h2 : x.2.val ≤ j.root.2.val) (z : V n) (c : ℂ) :
    cellPot ε G x (z + c • coordVec (ε.symm (.inr j))) = cellPot ε G x z := by
  have hb : bsL ε (z + c • coordVec (ε.symm (.inr j))) = bsL ε z := by
    ext a
    simp [bsL_apply, coordVec]
  have hf (j' : Cell m) (h : j' ≠ j) : fb ε (z + c • coordVec (ε.symm (.inr j))) j' = fb ε z j' := by
    simp [fb, coordVec, h]
  unfold cellPot
  rw [hb]
  congr 2
  refine GlobalTheory.T.gradedSquaredLength_upperUnitriangular_gram_eq_of_agree _ _ _ _ _ fun s hs => hf _ ?_
  rintro rfl
  exact h1 (Sigma.ext rfl (heq_of_eq (le_antisymm hs h2)))

theorem dens_cellForm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  intro ι _ m n d ε G a w hG hC
  have e : cellFib ε G w = ∏ x : Root m, (∑ p, ∑ q,
      (kappa * -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) • sym (p, q)) ^ (m x.1 - 1 - x.2 : ℕ) := by
    simp only [cellFib, fibrePoint, map_prod, map_pow, map_neg, map_X, aeval_X, ofValues, ddc, mul_neg, neg_smul,
      Finset.sum_neg_distrib]
  have hk : kappa ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [kappa, hπ]
  rw [cellForm, e, dens_blocks n d (Cell m) (Root m) ε Cell.root (fun x => x.2.val)
    (fun x p q => -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) (fun x => m x.1 - 1 - x.2)
    (fun x => by convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w x (hG _) (hC _)).1.symm) ?_]
  · congr 1
    rw [fibDens, Fintype.prod_sigma, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density _ _ (hG τ), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    · push_cast
      rfl
    · convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w ⟨τ, i⟩ (hG _) (hC _)).2 <;> rfl
  · intro x j h1 h2 b
    have h := GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant n (cellPot ε G x) w (coordVec (ε.symm (.inr j))) (coordVec b)
      (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m n d ε G w x (hG _) (hC _)).1 (cellPot_add ε G x j h1 h2)
    simp only [ddc, mul_eq_zero, hk, false_or] at h
    simp [h.1, h.2]

end GlobalTheory.FlagCell2.CellDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem GlobalTheory.cmTorsionConj : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') → (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  intro hPC hAD hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E _ _ _ _ I _ φ hCM hres c y hc 𝔠 T X' p hpb u' htan
    x x' hxx'
  have hTT' := hTT
  obtain ⟨hΩ₀, hΩ₁, hgio, hΛ₀, -, hg₂, hg₃, -⟩ := hTT'
  have hW : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁ := curve_map (g : ℂ →+* ℂ) hg₂ hg₃
  obtain ⟨hU1, hE2, hE3⟩ := GlobalTheory.T.conjugate_group_points_injective_mul T.X.A X'.A g p hpb.grp
  obtain ⟨m, b, a, a', hbL, hx', hxL, hint⟩ := GlobalTheory.T.lattice_approximation_upward_idele K E t c y hc x x' hxx'
  have hlat : ∀ z ∈ lattice c y, (fun j ↦ φ (T.U.e j) z) ∈ T.U.u.Λ := fun z hz =>
    (T.U.lat _).2 ⟨z, hz, funext fun j => by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have hφK : ∀ i (r : K), φ i (algebraMap K E r) = io r := fun i r => by rw [← RingHom.comp_apply, hres i]
  have hpt : ∀ z, pt Λ₁ Ω₁ z ≫ toSpec (curve Λ₁ Ω₁) = 𝟙 _ := fun z => by
    rw [pt, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; simp
  have key : ∀ k, (u'.ex (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k)))).left ≫ p =
      spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k))).left := by
    intro k
    set β : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ φ (T.U.e j) (b k) with hβdef
    have hβ : ∀ l ∈ Λ₀.lattice, l • β ∈ T.U.u.Λ := by
      intro l hl
      obtain ⟨r, hr, rfl⟩ := ((GlobalTheory.LatVal.CurveTransport.isLatOf_iff).1 hΛ₀ l).1 hl
      obtain ⟨r', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hr
      have h1 := hlat _ (hbL k r')
      convert h1 using 1
      funext j
      simp [β, hφK]
    obtain ⟨f, hfo, hf⟩ := GlobalTheory.T.elliptic_curve_map_to_abelian (FR E) 𝔠 T.X T.U.c _ T.U.u Λ₀ Ω₀ hΩ₀ β hβ
    have hsq : (mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f) ≫ T.X.A.hom =
        toSpec (curve Λ₁ Ω₁) ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, hfo, GlobalTheory.WeierstrassCurve.mapHom_toSpec]
    let f' := hpb.grp.1.lift _ _ hsq
    have hf'p : f' ≫ p = mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f := hpb.grp.1.lift_fst _ _ _
    have hf'o : f' ≫ X'.A.hom = toSpec (curve Λ₁ Ω₁) := hpb.grp.1.lift_snd _ _ _
    let e' : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X'.A) := fun z => Over.homMk (pt Λ₁ Ω₁ z ≫ f') (by
      rw [Category.assoc, hf'o, hpt]; rfl)
    have hD3 := GlobalTheory.T.conjugate_curve_point_addition_compat Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ hW
    have hover : ∀ z z', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z →
        (e' z').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (z • β)).left := by
      intro z z' hzz
      show (pt Λ₁ Ω₁ z' ≫ f') ≫ p = _
      rw [Category.assoc, hf'p, ← Category.assoc, hzz, Category.assoc, hf]
    have hadd : ∀ z' w', e' (z' + w') = e' z' * e' w' := by
      intro z' w'
      obtain ⟨z, hz⟩ := hD3.1 z'
      obtain ⟨w, hw⟩ := hD3.1 w'
      apply hU1
      rw [hover _ _ (hD3.2 z w z' w' hz hw), hE2 _ _ _ _ (hover _ _ hz) (hover _ _ hw), add_smul, T.U.u.ex_add]
    obtain ⟨β₁, hβ₁⟩ := GlobalTheory.T.elliptic_map_uniformization_line (FR E) 𝔠 X' T.U.c _ u' Λ₁ Ω₁ hΩ₁ f' hf'o e' hadd (fun z => rfl)
    let v : epsR ℂ ⟶ T.X.A := Over.homMk (tan (curve Λ₀ Ω₀) Ω₀ ≫ f) (by
      rw [Category.assoc, hfo, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    let v' : epsR ℂ ⟶ X'.A := Over.homMk (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') (by
      rw [Category.assoc, hf'o, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    obtain ⟨-, hv⟩ := GlobalTheory.T.elliptic_map_tangent_differential T.X.A _ _ T.U.u Λ₀ Ω₀ hΩ₀ f β hf Ω₀ v rfl
    obtain ⟨hv't, hv'⟩ := GlobalTheory.T.elliptic_map_tangent_differential X'.A _ _ u' Λ₁ Ω₁ hΩ₁ f' β₁ hβ₁ ((g : ℂ →+* ℂ) Ω₀) v' rfl
    rw [div_self hΩ₀, one_smul] at hv
    have hvv : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
      show (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') ≫ p = _ ≫ (tan (curve Λ₀ Ω₀) Ω₀ ≫ f)
      rw [Category.assoc, hf'p, ← Category.assoc, GlobalTheory.T.conjugate_curve_tangent_compat _ _ (g : ℂ →+* ℂ) hW Ω₀, Category.assoc]
    have h1 := htan β v v' hvv hv
    have heq := GlobalTheory.T.tangent_differential_unique X'.A _ _ u' v' _ _ hv't hv' h1
    have hgΩ : g Ω₀ ≠ 0 := (map_ne_zero g).2 hΩ₀
    have hβ₁eq : β₁ = fun j ↦ g (β j) := by
      funext j
      have h2 := congrFun heq j
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] at h2
      field_simp at h2
      exact h2
    have hd1 := GlobalTheory.T.conjugate_torsion_point_compat K io g t Λ₀ Λ₁ Ω₀ Ω₁ hTT hW (a k) (a' k) (hint k)
    have e1 : (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) = io (a' k) • β₁ := by
      rw [hβ₁eq]; funext j; simp [β, hφK, hgio]
    have e2 : (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) = io (a k) • β := by
      funext j; simp [β, hφK]
    rw [e1, e2, ← hβ₁, Category.assoc, hf'p, ← Category.assoc, hd1, Category.assoc, hf]
  have exsum : ∀ {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {n : ℕ} (uu : HolUnif A L n)
      (w : Fin m → Fin n → ℂ), uu.ex (∑ k, w k) = ∏ k, uu.ex (w k) := by
    intro A _ _ L n uu w
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simpa using (uu.ker 0).2 (zero_mem _)
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, uu.ex_add, ih]
  have hsum' : (fun j ↦ g (φ (T.U.e j) x')) = ∑ k, (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) := by
    rw [hx']; funext j; simp [map_sum]
  have hsum : (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) =
      ∑ k, (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) := by
    funext j; simp [map_sum]
  have hxm : T.U.u.ex (fun j ↦ φ (T.U.e j) x) =
      T.U.u.ex (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) := by
    have h1 := hlat _ hxL
    have e3 : (fun j ↦ φ (T.U.e j) x) = (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) +
        (fun j ↦ φ (T.U.e j) (x - ∑ k, algebraMap K E (a k) * b k)) := by
      funext j; simp
    rw [e3, T.U.u.ex_add, (T.U.u.ker _).2 h1, _root_.mul_one]
  rw [hxm, hsum', hsum, exsum, exsum]
  exact hE3 (Fin m) Finset.univ _ _ (fun k _ => key k)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNorm
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem torsor_point_of_essFiniteType : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  obtain ⟨A', _, _, _, _, _, _, EA', _, _, _, _, _, QA', _, hQ', hq', ρ', hρ1, hρ2, jA', ψA', hψ', DA', _, _,
    actA', htor', hgood', β, h, hβ1, hβ2⟩ :=
    GlobalTheory.T.strictHenselisation_enlarge_good_at_origin T O hT P φ hφ hsh hP q hq0 hqT A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htor
  have hce := GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType A' EA' QA' hQ' ρ' hρ1 hρ2 q hq0 hq' DA' actA' htor' hgood'
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsSepClosed (ResidueField O) := hsh.2.1
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian A' (Localization.AtPrime QA') O (GlobalTheory.LocAcyc.GenFib T O) jA'
    (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)) ψA' hψ' DA' htor'.1 hce
  refine ⟨σ'.comp h, ?_⟩
  rw [RingHom.comp_assoc, hβ2, ← RingHom.comp_assoc, hσ', hβ1]

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_equivariant_bijection_transport_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  first | exact @GlobalTheory.Mum.trait_transport | exact GlobalTheory.Mum.trait_transport | (intros; apply GlobalTheory.Mum.trait_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_corrDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ
  refine ⟨fun i j y hy hi hj => ?_, fun i => ?_⟩
  · exact GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo j hy hi hj (E.nonempty (under y)).choose_spec
  · refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density i.e (isOpen_ptsIn O) fun y hy hc => ?_
    set A := (E.nonempty (under y)).choose with hAdef
    have hA : A ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
    refine ⟨corrTop (fun v => ρ (i.e.symm v)) (fun v => H₀ A (i.e.symm v) ()) (fun v => H A (i.e.symm v) ()), ?_, ?_⟩
    · have hs : i.e.target ∩ i.e.symm ⁻¹' Set.univ ∈ 𝓝 (i.e y) := by
        simpa using i.e.open_target.mem_nhds (i.e.map_source hc)
      have hρ1 : ContDiffAt ℝ 1 (fun v => ρ (i.e.symm v)) (i.e y) :=
        ((contDiffOn_chart (S := Set.univ) (fun z _ => hρ z) i).contDiffAt hs).of_le (by norm_cast)
      have hc0 := GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρ1 (hM₀.mContDiffAt_chart mem_ptsIn_top i hc hA ())
        (hM₀.isUnit_det_chart mem_ptsIn_top i hc hA ()) (hM.mContDiffAt_chart hy i hc hA ())
        (hM.isUnit_det_chart hy i hc hA ())
      exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hc0)
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, i.e.open_source.mem_nhds hc, GlobalTheory.FrameLift.eventually_mem hA]
        with z hzO hzc hAz
      have h := GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo i hzO hzc hzc hAz
      rw [AlgChart.transDet_self i hzc, norm_one, one_pow, one_mul] at h
      exact h.symm

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_const_point {S : Type} [CommRing S] {A : Over (Sp S)} (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal c f = 0 := by
  have e : GlobalTheory.GrpTangent.epsScale (0 : S) ≫ c = c := by
    refine Over.OverMorphism.ext ?_
    have h := Over.w (GlobalTheory.GrpTangent.epsScale (0 : S))
    rw [Over.comp_left, hc, ← Category.assoc]
    exact congrArg (· ≫ p) h
  rw [← e, tanVal_epsScale, zero_mul]

theorem isTangent_iff_reduction_eq_one {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] (z : epsR S ⟶ A) :
    IsTangent z ↔ spOver (TrivSqZeroExt.fstHom S S S) ≫ z = 1 := by
  have h1 : (1 : Over.mk (spMap (algebraMap S S)) ⟶ A).left = η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    have : (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S)))).left = 𝟙 (Sp S) := by
      have h := Over.w (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S))))
      refine (Category.comp_id _).symm.trans (h.trans ?_)
      exact Spec.map_id _
    rw [this]
    exact Category.id_comp _
  constructor
  · intro h
    exact Over.OverMorphism.ext (h.trans h1.symm)
  · intro h
    exact (congrArg Over.Hom.left h).trans h1

theorem translate_const (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) (S : Type) [CommRing S]
    (A : Over (Sp S)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (y : epsR S ⟶ A) :
    (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left =
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧
      ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  refine ⟨?_, fun f ↦ ?_⟩
  · rw [isTangent_iff_reduction_eq_one, MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
    exact ⟨fun h ↦ Over.OverMorphism.ext h, fun h ↦ congrArg Over.Hom.left h⟩
  · have h := tanVal_mul_all hC hH S A g hA hg f (y * c⁻¹) c
    rw [inv_mul_cancel_right, tanVal_const_point c p hc f, add_zero] at h
    exact h

end GlobalTheory.TanAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistKernel

theorem twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL ha T _ hT N hN
  have := hA.proper
  have : LocallyOfFiniteType (A ⊗ T).hom := by
    have := hT
    first
    | infer_instance
    | (show LocallyOfFiniteType (pullback.fst A.hom T.hom ≫ A.hom); infer_instance)
    | (show LocallyOfFiniteType (pullback.snd A.hom T.hom ≫ T.hom); infer_instance)
  have : IsLocallyNoetherian (A ⊗ T).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ T).hom
  have hΛ : Fam A (abelian₂ A L) := ⟨LB.isLB_linComb hL _ _,
    (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL (LB.isLB_linComb hL _ _)).1⟩
  obtain ⟨H, h, hh, hH⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp R) A (A ⊗ T) hA
    (ev (abelian₂ A L) (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T)) (ev N (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
    (hΛ.ev (fst A T)) (hN.ev (snd A T))
  have rep : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T),
      Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
    intro Y a t
    rw [← hH Y (lift a t), same_iff hΛ.isLB hN.isLB, same_iff (hΛ.ev (fst A T)).isLB (hN.ev (snd A T)).isLB,
      evc_ev hΛ.isLB, evc_ev hN.isLB]
    simp
  exact ⟨H, h, hh, GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep,
    GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter R A hA L hL ha T hT N hN H h hh rep (GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep),
    GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily R A hA L hL ha T hT N hN H h hh rep, rep⟩

end GlobalTheory.TwistKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAddStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  first | exact @GlobalTheory.MumCmp.Transl.pG_comp_lift_translate | exact GlobalTheory.MumCmp.Transl.pG_comp_lift_translate | (intros; apply GlobalTheory.MumCmp.Transl.pG_comp_lift_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_closedFibre_subset_isAffineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) →
    ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR _ _ G _ _ hG _ s hs
  exact GlobalTheory.T.exists_affineOpen_finset_closedFibre_semiAbelian R hR.1 G hG s hs

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegTh.CmpUnif.cmp_unif | exact GlobalTheory.SiegTh.CmpUnif.cmp_unif | (intros; apply GlobalTheory.SiegTh.CmpUnif.cmp_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  first | exact @GlobalTheory.UPoinc.ULift.labels_lift | exact GlobalTheory.UPoinc.ULift.labels_lift | (intros; apply GlobalTheory.UPoinc.ULift.labels_lift <;> assumption)
end

