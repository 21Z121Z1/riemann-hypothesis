import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0021
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0009
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0020
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  first | exact @GlobalTheory.JetPointBC.unit_law_act_baseChange | exact GlobalTheory.JetPointBC.unit_law_act_baseChange | (intros; apply GlobalTheory.JetPointBC.unit_law_act_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  first | exact @GlobalTheory.jetPoints_laws_iff_pullback | exact GlobalTheory.jetPoints_laws_iff_pullback | (intros; apply GlobalTheory.jetPoints_laws_iff_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nabValN_congr_FK {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) (B' : FB R' d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [Algebra R' k]
    (hF : B'.FK k = B.FK k) (hA : ∀ a, B'.actK k a = B.actK k a)
    (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {κ : Type} [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    nabValN B k h w0 m f cp u P = nabValN B' k h w0 m f cp u P := by
  unfold nabValN FB.hL
  rw [hF, hA]

theorem isIntPS_iff_exists_map (T : CDVR) {n d : ℕ} (f : PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro hf
    choose g hg using hf
    refine ⟨g, ?_⟩
    ext m
    exact (MvPowerSeries.coeff_map _ _ _).trans (hg m)
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem nuLocC_eq_nuAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  intro E _ _ _ H Dw l Xo c _ T io y C
  letI := io.toAlgebra
  intro BT hF hA e k a n
  unfold nuLocC nuAlg
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    refine iInf_le_of_le (MvPowerSeries.map (algebraMap T.V T.Fr) g) ?_
    refine iInf_le_of_le ((isIntPS_iff_exists_map T _).2 ⟨g, rfl⟩) ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _))
  · refine le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨g, rfl⟩ := (isIntPS_iff_exists_map T _).1 hf
    refine iInf_le_of_le g ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _)).symm

end GlobalTheory.ChartCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.JCalc

variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

theorem jeq_refl (f : MvPowerSeries σ R) : JEq m f f := fun _ _ => rfl

theorem jeq_add {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f + g) (f' + g') :=
  fun e he => by rw [map_add, map_add, h e he, k e he]

theorem jeq_sub {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f - g) (f' - g') :=
  fun e he => by rw [map_sub, map_sub, h e he, k e he]

theorem jeq_mul {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f * g) (f' * g') := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
  rw [map_add] at hsum
  rw [h p.1 (by omega), k p.2 (by omega)]

theorem jeq_cancel {f g u : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff u))
    (h : JEq m (f * u) (g * u)) : JEq m f g := by
  obtain ⟨c, hc⟩ := hu
  have h1 := MvPowerSeries.mul_invOfUnit u c hc.symm
  have := jeq_mul h (jeq_refl (MvPowerSeries.invOfUnit u c))
  rwa [_root_.mul_assoc, _root_.mul_assoc, h1, _root_.mul_one, _root_.mul_one] at this

theorem jeq_map {R' : Type} [CommRing R'] (β : R →+* R') {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) :=
  fun e he => by rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

theorem jeq_iff_truncTotal [Finite σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ MvPowerSeries.truncTotal (m + 1) f = MvPowerSeries.truncTotal (m + 1) g := by
  constructor
  · intro h
    ext e
    by_cases he : e.degree ≤ m
    · rw [MvPowerSeries.coeff_truncTotal _ (by omega), MvPowerSeries.coeff_truncTotal _ (by omega), h e he]
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega), MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]
  · intro h e he
    rw [← MvPowerSeries.coeff_truncTotal (n := m + 1) f (by omega),
      ← MvPowerSeries.coeff_truncTotal (n := m + 1) g (by omega), h]

theorem jeq_subst [Finite σ] {τ : Type} [Finite τ] {a a' : σ → MvPowerSeries τ R} {f g : MvPowerSeries σ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, JEq m (a i) (a' i)) (k : JEq m f g) :
    JEq m (MvPowerSeries.subst a f) (MvPowerSeries.subst a' g) := by
  rw [jeq_iff_truncTotal] at k ⊢
  simp only [jeq_iff_truncTotal] at h
  rw [MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha', k]
  simp only [h]

theorem jet_mk_eq_zero_iff (p : MvPolynomial σ R) :
    (Ideal.Quotient.mk _ p : Jet R σ m) = 0 ↔ ∀ e : σ →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  have h : orig R σ = MvPolynomial.idealOfVars σ R := rfl
  rw [Ideal.Quotient.eq_zero_iff_mem, h, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE_iff [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc_ite [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE_iff]

theorem jeq_iff_psJet [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ psJet m f = psJet m g := by
  rw [← sub_eq_zero (a := psJet m f), psJet, psJet, ← map_sub, jet_mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_ite, coeff_psTrunc_ite, if_pos he, if_pos he, sub_eq_zero]

theorem eq_of_jeq {f g : MvPowerSeries σ R} (h : ∀ m', JEq m' f g) : f = g :=
  MvPowerSeries.ext fun e => h _ e le_rfl

theorem jeq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) :=
  fun _ _ _ =>
  ⟨fun _ _ _ _ _ h k => ⟨jeq_add h k, jeq_sub h k, jeq_mul h k⟩,
    fun _ _ _ _ hu h => jeq_cancel hu h,
    fun _ _ _ β _ _ h => jeq_map β h,
    fun _ _ _ _ _ _ _ ha ha' h k => jeq_subst (fun p => ha p.1 p.2) (fun p => ha' p.1 p.2) (fun p => h p.1 p.2) k,
    fun _ _ _ f g => jeq_iff_psJet f g,
    fun _ _ _ h => eq_of_jeq h⟩

end GlobalTheory.ChartCmp.JCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveIsoG_passes_to_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.primG_pullback | exact GlobalTheory.primG_pullback | (intros; apply GlobalTheory.primG_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveIsoG_unique_on_abelian : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t, IsPrimG t wP → IsPrimG t wP' → wP = wP' := by
  first | exact @GlobalTheory.isPrimG_unique | exact GlobalTheory.isPrimG_unique | (intros; apply GlobalTheory.isPrimG_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidificationAtOrigin_baseChange_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  first | exact @GlobalTheory.rigidificationAtOrigin_baseChange | exact GlobalTheory.rigidificationAtOrigin_baseChange | (intros; apply GlobalTheory.rigidificationAtOrigin_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidificationAtOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  first | exact @GlobalTheory.rigOrigin_iff_pullback | exact GlobalTheory.rigOrigin_iff_pullback | (intros; apply GlobalTheory.rigOrigin_iff_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedIso_maps_cubical_generator : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → IsAbelianScheme t'.G → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) := by
  first | exact @GlobalTheory.RigCub.rigIso_cub | exact GlobalTheory.RigCub.rigIso_cub | (intros; apply GlobalTheory.RigCub.rigIso_cub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMap
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushSecondLaw

open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw

section Values

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}

theorem val_pmaps {φ : K → (Y ⟶ X)} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val t (r ≫ h) z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have e := H _ r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ _) (fun k => hJ' _)
  refine Eq.trans ?_ e
  refine val_of _ _ _ _ _ fun k => congrArg J ?_
  rw [Category.assoc, Category.assoc, hc]

theorem val_carries {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by
  have P : PMaps w φ' (fun k => φ' k ≫ F) ε g c (𝟙 Y') :=
    (maps_iff w φ' _ ε g c (𝟙 Y') (flatGen L F φ' ε c) (fun j => wchart_pull_le L F φ' j) (fun j => rfl)).1 H
  have e := val_pmaps P (fun k => (Category.id_comp _).symm) hJ hJ' r
  rwa [Category.comp_id] at e

end Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleGenG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (c : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

set_option maxHeartbeats 4000000 in

theorem prod_second_law {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I) :
    ∏ I, h ((lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
        (jptG t x0 d x m (0 : Fin 3)))).left ≫ thφ t.G (x3 t.G) I) ^ thε I =
      P ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] *
        ((P ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])⁻¹ *
          (P ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])⁻¹) := by
  have hQ : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h (psum t.G
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m,
        Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m] I.down).left ^ cε 2 I := fun φ => by
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    exact (hP φ).trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (pe_pt m _ I))
  simp only [hQ, th_pt, Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_law hch]
  erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  rw [prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
    prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  have ha2 : jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3) =
      jptG t x0 d x m (1 : Fin 3) * (jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3)) := _root_.mul_assoc _ _ _
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
  erw [ha2]
  abel!

theorem lift_comp_cube {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (n : CubeMap G G') {T : Over S} {a b c : T ⟶ G} {a' b' c' : T ⟶ G'} (ha : a'.left = a.left ≫ n.F)
    (hb : b'.left = b.left ≫ n.F) (hc : c'.left = c.left ≫ n.F) :
    (lift a' (lift b' c')).left = (lift a (lift b c)).left ≫ n.F3 := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i
  · simpa [x3] using ha
  · simpa [x3] using hb
  · simpa [x3] using hc

theorem alg_step {U : Type} [CommGroup U] {θ θ' u A B C A' B' C' p a b c : U} (k : θ = u * (A * (B⁻¹ * C⁻¹)))
    (hθ : θ' = p * θ) (hA : A' = a * A) (hB : B' = b * B) (hC : C' = c * C) (hp : p = a * (b⁻¹ * c⁻¹)) :
    θ' = u * (A' * (B'⁻¹ * C'⁻¹)) := by
  subst k hθ hA hB hC hp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem famPh2_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hfr F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J' hJ' => ?_⟩
  choose J hJ using fun χ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  replace hJ : Good t.PP.L y J := hJ
  obtain ⟨W, hW⟩ : ∃ W : ((jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left) → ((jOG (𝟙 (Sp V)) d m 3).left.presheaf.stalk y)ˣ,
    W = fun q => gw w q y (J' (q ≫ n.φ)) (J q) := ⟨_, rfl⟩
  obtain ⟨-, c, -, hc, hcar⟩ := hfr m
  have hpt : ∀ i : Fin 3, (jptG t' (𝟙 (Sp V)) d x' m i).left = (jptG t (𝟙 (Sp V)) d x m i).left ≫ n.φ := fun i => by
    rw [jptG, jptG, Over.comp_left, Over.comp_left, hx m, Category.assoc]
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J' =
        (∏ I : ULift.{0} (Finset (Fin 2)), W ((homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J := fun φ => by
    refine (val_pull hJ' _ _ _).trans ((val_corr hJ' hc _).symm.trans ((val_carries hcar hJ' hJ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _).symm
    rw [hW, Category.id_comp]
  have P : PMaps w (thφ t.G (x3 t.G)) (thφ t'.G (x3 t'.G)) thε t.cub.t t'.cub.t n.cm.F3 :=
    (maps_iff w _ _ thε t.cub.t t'.cub.t n.cm.F3 _ (fun j => n.cm.theta_le t'.PP.L j) (fun j => rfl)).1 hcub.2
  have hθ := val_pmaps P (fun I => n.cm.psum_comm I.down) hJ' hJ
    (lift (jptG t (𝟙 (Sp V)) d x m (1 : Fin 3)) (lift (jptG t (𝟙 (Sp V)) d x m (2 : Fin 3))
      (jptG t (𝟙 (Sp V)) d x m (0 : Fin 3)))).left
  rw [← hW, ← lift_comp_cube n.cm (hpt 1) (hpt 2) (hpt 0)] at hθ
  have k := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcor (𝟙 _)).trans ((val_scaleGenG t hJ _ _ _).trans
    (congrArg _ ((val_mul hJ _ _ _).trans (congrArg _ ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  rw [Category.id_comp] at k
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_scaleGenG t' hJ' _ _ _).trans
    (congrArg _ ((val_mul hJ' _ _ _).trans (congrArg _ ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  rw [Category.id_comp]
  exact alg_step k hθ (hpe _) (hpe _) (hpe _) (prod_second_law hch m W _ (fun _ => rfl))

end GlobalTheory.PushSecondLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ModelSquareFunctions

theorem isProper_genericFibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
  have h1 := I.m1.cart.1
  have h2 := I.m2.cart.1
  have hp : IsProper I.t'.G.hom := MorphismProperty.of_isPullback h1 Xo.univ.proper
  show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V (FractionRing T.V))))
  rw [← h2.isoPullback_inv_snd]
  infer_instance

theorem surjective_appTop_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  intro E _ _ _ H Dw l Xo c T io y I
  have h := (globalFnsDvr_of_globalFns GlobalTheory.globalFns_holds E H T.V T.cpl I.G (isProper_genericFibre I) 2).2
  let e : powObj I.G.G 2 ≅ I.G.G ⊗ I.G.G := I.G.G ◁ᵢ (ρ_ I.G.G)
  have hw : e.inv.left ≫ (powObj I.G.G 2).hom = (I.G.G ⊗ I.G.G).hom := Over.w e.inv
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (e.inv.left.app ⊤))
  rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso e.inv.left.appTop).2.comp h

end GlobalTheory.ModelSquareFunctions
end
end

