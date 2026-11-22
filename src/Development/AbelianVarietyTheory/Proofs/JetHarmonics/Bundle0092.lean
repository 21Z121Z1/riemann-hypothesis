import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap F (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  first | exact @GlobalTheory.exists_boxFam_multilinear | exact GlobalTheory.exists_boxFam_multilinear | (intros; apply GlobalTheory.exists_boxFam_multilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExactTerm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem exists_val_eq_of_nonneg [IsAlgClosed F] (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 ≤ r) :
    ∃ c : F, v c = ((r : ℚ) : WithTop ℚ) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact ⟨1, by rw [AddValuation.map_one]; rfl⟩
  · obtain ⟨c, -, hc⟩ := exists_val_eq hv hr
    exact ⟨c, hc⟩

theorem nuGe_of_single (hϖ : Irreducible ϖ) (hQ : QForm.IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) (α : D.toPre.X) (r : ℚ)
    (hs : ∀ β : D.toPre.X, (∀ mu, α + k • mu ≠ β) → ∀ j, (s.s β).f j = 0)
    (h : VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)) : NuGe D Q F v k s r := by
  intro β
  by_cases hβ : ∃ mu, α + k • mu = β
  · obtain ⟨m0, rfl⟩ := hβ
    have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s h
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e : r + (Q α : ℚ) / k + ((k * Q m0 + QForm.bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
      rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
    rwa [e] at H
  · exact vge_of_zero (hs β fun mu e => hβ ⟨mu, e⟩) _

theorem pullAl_zero {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} {a : O} {k N : ℕ}
    {s : Fam D.toPre F k} {s' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s s') (χ : D.toPre.X)
    (h0 : ∀ j, (s.s χ).f j = 0) : ∀ j, (s'.s (star a • χ)).f j = 0 := by
  intro j
  obtain ⟨u, -, -, hrel⟩ := h.1 χ
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} {p : QkPt D.toPre F k}
    {w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s t : Fam D.toPre F k} (h : PhiRel D.toPre F k p w s t) (α : D.toPre.X)
    (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (t.s (α + p.y)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG p w hw α
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

end

theorem main : Laws → TwistBCSpanStatement → TWM.VRatioGtStatement → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : O) → ∀ (p : QkPt D.toPre F (k * N)) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (k * N)))), w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F (k * N) p w ζ → ∀ χ₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ ∀ s' t h : Fam D.toPre F (k * N), PullAl D F oa a k N s s' → PhiRel D.toPre F (k * N) p w s' t → Fam.IsSmul D.toPre F ζ t h → NuGe D Q F v (k * N) h 0 ∧ (∀ β : D.toPre.X, (∀ z, β ≠ p.y + star a • χ₀ + k • star a • z) → ∀ j, (h.s β).f j = 0) ∧ ∃ x : F, Val0 D F (k * N) (star a • χ₀ + p.y) (h.s (star a • χ₀ + p.y)) x ∧ v x = (((Q (star a • χ₀ + p.y) : ℚ) / (k * N) : ℚ) : WithTop ℚ) := by
  intro hL hTW hVR hUU V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv O _ _ _ oa w0 hw0 a N k hN hk haa p w hw ζ hζ hfin χ₀
  have hG := hL.globalFns
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  have haa' : star a * a = (N : O) := by rw [mul_comm, haa]
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hval⟩ :=
    GlobalTheory.exists_integral_section_unit_at hL hTW V ϖ hϖ D Q hQ F v hv k hk χ₀ (m ≫ oa.onB.act a)
  have hQ0 : (0 : ℚ) ≤ Q χ₀ := by
    by_cases hχ : χ₀ = 0
    · subst hχ; rw [QForm.Q_zero hϖ D hQ]; simp
    · have := QForm.Q_pos hϖ D hQ hχ; exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ₀)
  obtain ⟨c, hc⟩ := exists_val_eq_of_nonneg hv (div_nonneg hQ0 (Nat.cast_nonneg k))
  obtain ⟨s₀, rfl, hs₀⟩ := GlobalTheory.FamFree.exists_fam_single hG D.tau_bimult hk1 χ₀ σ
  have hsupp : ∀ β : D.toPre.X, (∀ mu, χ₀ + k • mu ≠ β) → ∀ j, ((c • s₀).s β).f j = 0 := fun β hβ j => by
    rw [smul_f, hs₀ β hβ j, mul_zero]
  have hnu : NuGe D Q F v k (c • s₀) 0 :=
    nuGe_of_single hϖ hQ hv hk1 _ χ₀ 0 hsupp (hσ.smul hc.ge fun j => rfl)
  refine ⟨c • s₀, hnu, fun s' t h hP hΦ hsm => ⟨?_, fun β hβ j => ?_, ?_⟩⟩
  · exact (galois_fixed_adelic_matrices_descend hL (TWM.tw_of hG hTW hVR) V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin s' t h hΦ hsm 0).1
      (pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL) V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N hN haa haa' k hk1
        _ s' hP 0 hnu)
  · obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
    have h1 : ∀ j, (s'.s α).f j = 0 := by
      by_cases hα : ∃ χ, α = star a • χ
      · obtain ⟨χ, rfl⟩ := hα
        refine pullAl_zero hP χ (hsupp χ ?_)
        rintro mu rfl
        refine hβ mu ?_
        rw [smul_add, smul_comm (star a) k mu]
        abel
      · exact hP.2 α fun χ e => hα ⟨χ, e⟩
    refine (hsm _ j).trans ?_
    rw [phiRel_zero hG hw hΦ α h1 j]
    exact mul_zero _
  · have hpull := GlobalTheory.pullAl_value_integral_point hL V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N k hN hk1 haa _ s' hP χ₀ m
      ((Q χ₀ : ℚ) / k) ⟨G₀, hG₀, c * x, by rw [AddValuation.map_mul, hc, hx, ← WithTop.coe_add, add_zero],
        fun z J hJ => by
          rw [sval_smul c s₀ χ₀ _ z hJ, hval z J hJ, ← Over.comp_left, lift_fst, Over.id_left, map_mul,
            gs_mul _ z ⊤ trivial, _root_.mul_assoc]⟩
    obtain ⟨y, hy, hvy⟩ := GlobalTheory.PhiValue.main hL hTW hVR hUU V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin
      s' t h hΦ hsm (star a • χ₀) m hm _ hpull
    refine ⟨y, hy, hvy.trans (congrArg _ ?_)⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ₀]
    push_cast
    field_simp
    ring

end GlobalTheory.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y

variable (Y) in

def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

def exponentOfOuter {n : ℕ} (x x' : Fin n → Y) (hl : IsPosHerm E (outer E x x')) : Exponent E Y where
  form := AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun y' => outer E x x' y y')
      (fun y' y'' => by simp [outer, mul_add, Finset.sum_add_distrib]))
    (fun y y'' => by ext y'; simp [outer, add_mul, Finset.sum_add_distrib])
  smul_left a y y' := by simp [outer, Finset.mul_sum, mul_assoc]
  hermitian := hl.1
  pos τ y hy := hl.2 y hy τ

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem exists_outer (e : Exponent E Y) : ∃ (n : ℕ) (x x' : Fin n → Y),
    (∀ y y', e.form y y' = outer E x x' y y') ∧ IsPosHerm E (outer E x x') := by
  obtain ⟨D⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.nonempty_dualSystem E Y

  let g : Fin (D.n * D.n) ≃ Fin D.n × Fin D.n := finProdFinEquiv.symm
  let x : Fin (D.n * D.n) → Y := fun k => e.form (D.y (g k).1) (D.y (g k).2) • D.e (g k).1
  let x' : Fin (D.n * D.n) → Y := fun k => D.e (g k).2
  have hfo : ∀ y y', e.form y y' = outer E x x' y y' := by
    intro y y'
    rw [D.form_eq e y y']
    exact (Equiv.sum_comp g (fun p => y (e.form (D.y p.1) (D.y p.2) • D.e p.1) * bar E (y' (D.e p.2)))).symm
  refine ⟨D.n * D.n, x, x', hfo, ?_, ?_⟩
  · intro η η'
    rw [← hfo, ← hfo]
    exact e.hermitian η η'
  · intro η hη τ
    rw [← hfo]
    exact e.pos τ η hη

theorem exists_exponent (h : IsConj cj) {l : SymB cj Y →ₗ[ℝ] ℝ} (hl : Admissible l) :
    ∃ e : Exponent E Y, ∀ β, l β = pairing e (formsEquiv Y h β) := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨n, x, x', hpos, hval⟩ :=
    GlobalTheory.PointStepCompare.exists_exponent E (isBalancedSpace (Y := Y) h) l hl.1 hl.2
  refine ⟨exponentOfOuter x x' hpos, fun β => ?_⟩
  rw [hval β, GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum _ _ x x' (fun y y' => rfl)]
  rfl

theorem exists_functional (h : IsConj cj) {w : 𝓞 E} (hw : w + bar E w = 1) (e : Exponent E Y) :
    ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ ∀ β, l β = pairing e (formsEquiv Y h β) := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨n, x, x', hfo, hpos⟩ := exists_outer e
  obtain ⟨l, hi, hp, hl⟩ := GlobalTheory.PointStepCompare.exists_functional E (isBalancedSpace (Y := Y) h) hw hpos
  refine ⟨l, ⟨hi, hp⟩, fun β => ?_⟩
  rw [hl β, GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum e _ x x' hfo]
  rfl

theorem exponent_ext (h : IsConj cj) {e e' : Exponent E Y}
    (hp : ∀ β, pairing e (formsEquiv Y h β) = pairing e' (formsEquiv Y h β)) : e = e' := by

  have hdiag : ∀ (f : Exponent E Y) (η : Module.Dual (𝓞 E) Y) (τ : E →+* ℂ),
      pairing f (formsEquiv Y h ⟨GlobalTheory.PointStepCompare.rankOne E η τ,
        (isBalancedSpace h _).2 (GlobalTheory.PointStepCompare.rankOne_balanced E η τ)⟩) = (τ (f.form η η : E)).re / 2 := by
    intro f η τ
    obtain ⟨n, x, x', hfo, -⟩ := exists_outer f
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.pairing_of_sum f _ x x' hfo, hfo, GlobalTheory.PointStepCompare.re_outer E x x' η τ]
    rfl

  have him : ∀ (f : Exponent E Y) (η : Module.Dual (𝓞 E) Y) (τ : E →+* ℂ), (τ (f.form η η : E)).im = 0 := by
    intro f η τ
    have h2 : τ (f.form η η : E) = starRingEnd ℂ (τ (f.form η η : E)) := by
      conv_lhs => rw [f.hermitian η η]
      exact GlobalTheory.PointStepCompare.emb_bar E τ _
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    linarith
  have hself : ∀ η, e.form η η = e'.form η η := by
    intro η
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply RingOfIntegers.ext
    apply τ.injective
    apply Complex.ext
    · have h1 := hp ⟨GlobalTheory.PointStepCompare.rankOne E η τ,
        (isBalancedSpace h _).2 (GlobalTheory.PointStepCompare.rankOne_balanced E η τ)⟩
      rw [hdiag, hdiag] at h1
      linarith
    · rw [him e, him e']

  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, bar E a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply IsCMField.complexConj_ne_one (K := E)
    apply AlgEquiv.ext
    intro z
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
    have hu : ∀ u : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E u) = algebraMap (𝓞 E) E u := by
      intro u
      have := congrArg (fun t : 𝓞 E => (t : E)) (hcon u)
      simpa using this
    rw [map_div₀, hu, hu, AlgEquiv.one_apply]

  have hform : ∀ y y', e.form y y' = e'.form y y' := by
    intro y y'
    have expand : ∀ (f : Exponent E Y) (c : 𝓞 E), f.form (y + c • y') (y + c • y') =
        f.form y y + c * bar E c * f.form y' y' + bar E c * f.form y y' + c * bar E (f.form y y') := by
      intro f c
      simp only [map_add, AddMonoidHom.add_apply, f.smul_left, f.smul_right]
      rw [f.hermitian y y']
      ring
    have E1 := (expand e 1).symm.trans ((hself _).trans (expand e' 1))
    have E2 := (expand e a).symm.trans ((hself _).trans (expand e' a))
    rw [hself y, hself y'] at E1 E2
    simp only [map_one, one_mul, mul_one] at E1
    have hprod : (a - bar E a) * (e.form y y' - e'.form y y') = 0 := by
      linear_combination a * E1 - E2
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm ha
    · exact sub_eq_zero.1 h0
  cases e
  cases e'
  congr 1
  exact AddMonoidHom.ext fun y => AddMonoidHom.ext fun y' => hform y y'

def exponentEquiv (h : IsConj cj) {w : 𝓞 E} (hw : w + bar E w = 1) :
    Exponent E Y ≃ {l : SymB cj Y →ₗ[ℝ] ℝ // Admissible l} :=
  Equiv.ofBijective
    (fun e => ⟨(exists_functional h hw e).choose, (exists_functional h hw e).choose_spec.1⟩)
    ⟨fun e e' he => exponent_ext h fun β => by
      rw [← (exists_functional h hw e).choose_spec.2, ← (exists_functional h hw e').choose_spec.2]
      exact LinearMap.congr_fun (congrArg Subtype.val he) β,
    fun l => by
      obtain ⟨e, he⟩ := exists_exponent h l.2
      exact ⟨e, Subtype.ext (LinearMap.ext fun β =>
        ((exists_functional h hw e).choose_spec.2 β).trans (he β).symm)⟩⟩

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

section Host

open Formalism.BasicNotions

end Host

end GlobalTheory.LeastExponentCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem l2SG_of_ae_smul {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F G : Mx k r → Wp) (c : ℝ)
    (h : ∀ᵐ x ∂νq, F (Matrix.of x) = (c : ℂ) • G (Matrix.of x)) :
    PI.BesselPeriodGGP.l2SG νq F = ENNReal.ofReal (c ^ 2) * PI.BesselPeriodGGP.l2SG νq G := by
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow]
  congr 1
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg c), ← Real.norm_eq_abs, ← Complex.norm_real,
    ofReal_norm_eq_enorm]
  rfl

theorem scaled_bessel_isometric : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq l dd hDS hgap hok hS hl hd hnz
  refine ⟨Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 _, fun w hw => ?_⟩
  obtain ⟨v, hv, hlv⟩ := GlobalTheory.bessel_nonzero_on_translates hH k r ε mu R Wp z π l hDS hl.1 hnz
  obtain ⟨-, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  obtain ⟨-, -, hdd, hP⟩ := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS dd hd v hv (l v)
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hn : 0 < ‖l v‖ := norm_pos_iff.mpr hlv
  have hin : ⟪l v, l v⟫_ℂ = ((‖l v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; first | rfl | norm_cast | simp
  have hbe : ∀ y ∈ R.sm, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN y v (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l y := by
    intro y hy
    rw [(hl.2 y hy v hv).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hin]
  have hre : (⟪l v, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v (l v)⟫_ℂ).re = ‖l v‖ ^ 2 * ‖l v‖ ^ 2 := by
    rw [hbe v (hTK v hv), inner_smul_right, hin, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [l2SG_of_ae_smul νq _ (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v (l v))
    (Real.sqrt dd / ‖l v‖ ^ 2), hP w hw, hre, ← ENNReal.ofReal_mul (sq_nonneg _)]
  · congr 1
    rw [div_pow, Real.sq_sqrt hdd.le]
    field_simp
  · filter_upwards [hae] with x hx
    rw [hbe _ (hsm _ hx w hw), smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hn 2).ne']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVRStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupExpansion_bijective_of_completeDVR : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s := by
  first | exact @GlobalTheory.expandsG_bijective_of_dvr | exact GlobalTheory.expandsG_bijective_of_dvr | (intros; apply GlobalTheory.expandsG_bijective_of_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_datum_direct_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ), ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)), (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q := by
  first | exact @GlobalTheory.exists_datum_pow | exact GlobalTheory.exists_datum_pow | (intros; apply GlobalTheory.exists_datum_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosedStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFormProductSpan_left_mul_closed : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  first | exact @GlobalTheory.HatNF.SpanMul.span_mul | exact GlobalTheory.HatNF.SpanMul.span_mul | (intros; apply GlobalTheory.HatNF.SpanMul.span_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSumStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weighted_bessel_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  first | exact @GlobalTheory.coef_mul_split | exact GlobalTheory.coef_mul_split | (intros; apply GlobalTheory.coef_mul_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_powPolAV_eq_prod_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  first | exact @GlobalTheory.WeilPower.weilIs_pow_field | exact GlobalTheory.WeilPower.weilIs_pow_field | (intros; apply GlobalTheory.WeilPower.weilIs_pow_field <;> assumption)
end

