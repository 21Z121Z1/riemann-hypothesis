import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3435
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3345
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveWeights
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem vV_algebraMap_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem log_ofAdd_neg (m : ℤ) :
    WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m := by
  first | rfl | simp [WithZero.log] | exact WithZero.log_coe _

theorem isLocalHom_of_centred {Y : Scheme.{0}} {y : Y} {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal _ := hna
  have h0 : ν a ≠ 0 := by
    intro h
    rw [hν.2.2 a h, map_zero] at ha
    exact not_isUnit_zero ha
  have hlt := hν.2.1 a hm
  have hlog : WithZero.log (ν a) < 0 := by
    have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
    simpa using this
  have hv := hval a h0
  obtain ⟨u, hu⟩ := ha
  rw [← hu, vV_algebraMap_unit] at hv
  have : (0 : ℝ) < -((WithZero.log (ν a) : ℤ) : ℝ) := by
    have : ((WithZero.log (ν a) : ℤ) : ℝ) < 0 := by exact_mod_cast hlog
    linarith
  rw [hv] at this
  simp at this

set_option maxHeartbeats 2000000 in

theorem exists_space_order_le_phi : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  intro h1 h2 h3 h4
  refine ((GlobalTheory.T.cusp_value_le_phi_complement h1 h2 h3 h4).and (GlobalTheory.T.integral_frame_stalk_compatibility h1 h2 h3 h4)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩ := h
  refine ⟨C, hC, max x0 x1, fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy ν hν φ hφ => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  haveI hg : IsLocalHom g := isLocalHom_of_centred hν T g ρ hρ hval
  obtain ⟨w, hw0, hwb⟩ := hx x hx' ((le_max_left _ _).trans hle) ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt
  refine ⟨w.1, w.2, fun j' hj' => ?_⟩
  obtain ⟨u, hu⟩ := hx1 x hx' ((le_max_right _ _).trans hle) ι p hp i hi Y hY Z TF la w y T io y' g hg hpt j' hj'
  have hu0 : algebraMap T.V T.Fr (u : T.V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u.ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) ≠ 0 := by
    rw [hu]; exact mul_ne_zero hu0 hw0
  have hgerm : H0.germ j' y (memTop y) hj' w.1 ≠ 0 := by
    intro h; rw [h, map_zero, map_zero] at hg0; exact hg0 rfl
  have hne : ν (H0.germ j' y (memTop y) hj' w.1) ≠ 0 := fun h => hgerm (hν.2.2 _ h)
  refine ⟨hne, fun m hm => ?_⟩
  have hv := hval _ hne
  rw [hm, log_ofAdd_neg, hu, vV_mul hu0 hw0, vV_algebraMap_unit, zero_add] at hv
  have e : (m : ℝ) = ρ * (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) := by
    rw [← hv]; push_cast; ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hwb hρ.le

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  first | exact @GlobalTheory.UPoinc.UTrait.finrank_le_min | exact GlobalTheory.UPoinc.UTrait.finrank_le_min | (intros; apply GlobalTheory.UPoinc.UTrait.finrank_le_min <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_fibre_cechCocycles_combination_coefficient_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  first | exact @GlobalTheory.FibreH1.fibre_dim | exact GlobalTheory.FibreH1.fibre_dim | (intros; apply GlobalTheory.FibreH1.fibre_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreRemIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio.Closed

open GlobalTheory.KS GlobalTheory.KS.GlueDer

theorem gs_stalk {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 Y) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 Y) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a).symm

theorem exists_sval_stalk {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ J', Good L (r z) J' ∧ ∀ s : LB.Sec (LB.LinComb L φ ε),
      sval s r z J = (r.stalkMap z).hom (sval s (𝟙 Y) (r z) J') := by
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) φ (fun k => J (r ≫ φ k)) (fun a b e => by rw [e])
    (fun k => hJ (r ≫ φ k))
  refine ⟨J', hJ', fun s => ?_⟩
  rw [sval_of s (𝟙 Y) (r z) J' (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e k)]
  exact gs_stalk r z _ (hJ.mem φ r) _

section Op

variable {R : Type} [CommRing R] {G : Over (Sp R)} {n : ℕ} {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X}
  {dd : Fin n → Fld G.left} {D : R → R} (h : Heat G m L dd D) (hdd : ∀ a, IsField ⊤ (dd a))
include hdd

theorem rsT_op (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)) :
    rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
  have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
    fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
  have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
    fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
  have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
    fun r => res_const G.hom hO r
  have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
    rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
  rw [rsT_of_le hO, rsT_of_le hO]
  simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

theorem rem_eq (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) {A : Type} [CommRing A] (π : Γ(G.left, O) →+* A)
    (hΘ : ∀ a b, π (constFn G.hom O (h.Θ a b)) = 0) (F T g : Γ(G.left, O)) (hT : IsUnit T)
    (e : op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (F * T) =
      F * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O T + g * T) :
    π g - 2 * (k : A) * π (h.d i O F) = 2 * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
  have e₁ := congrArg π e
  have hs : ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O (F * T)) =
      π F * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O T) + π T * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.1 O le_top, map_add, map_mul, map_mul]
    ring
  simp only [op, map_add, map_sub, map_mul, map_sum, hΘ, zero_mul, Finset.sum_const_zero, sub_zero, map_ofNat, map_pow,
    map_natCast] at e₁
  rw [hs, (h.lift i).1.2.1 O hO, map_add, map_mul, map_mul] at e₁
  refine (hT.map π).mul_left_cancel ?_
  linear_combination -e₁

end Op

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem exists_term_germ (N : ℕ) (β : Q.X) (j : Q.P.L.ι) (V : Y.H.left.Opens) (hV : V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j)
    (y : Y.H.left) (hy : y ∈ V) : ∃ (J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι) (c : (Y.H.left.presheaf.stalk y)ˣ),
      Good Q.P.L (Y.q.left y) J' ∧ ∀ σ τ, IsTerm Y N β σ τ →
        gs (𝟙 _) y V (rsT (τ.f fun _ => j) V) = (Y.q.left.stalkMap y).hom (sval σ (𝟙 _) (Y.q.left y) J') * c.val := by
  obtain ⟨J, hJ, e⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => Y.q.left) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hV hy)
  obtain ⟨J', hJ', e'⟩ := exists_sval_stalk Q.P.isLB (DegPre.famφB Q β) (DegPre.famε N) Y.q.left y hJ
  refine ⟨J', val ((Y.Φ Y.H (𝟙 _)).s β) (𝟙 _) y J, hJ', fun σ τ hτ => ?_⟩
  have h1 := hτ Y.H (𝟙 _) y J hJ
  rw [Category.id_comp, e'] at h1
  refine Eq.trans ?_ h1
  have hle : V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => j) := Glue.le_wchart _ hV
  refine Eq.trans ?_ (sval_of τ (𝟙 _) y J (fun _ => j) (fun _ => by rw [Category.id_comp]; exact e ())).symm
  exact (congrArg (gs (𝟙 _) y V) (rsT_of_le hle _)).trans (gs_res (𝟙 _) y hle hy _)

theorem rem_chart (hdd : ∀ a, IsField ⊤ (dd a)) (N : ℕ) (β : Q.X) (σ σ' σp σp' : Q.SecB N β) (U : Q.P.A.left.Opens)
    (f g : Γ(Q.P.A.left, U)) (hr : IsRatio Q σ σ' U f) (h₁ : TActs Y h N β σ σp) (h₂ : TActs Y h N β σ' σp')
    (hg : IsRem Q σ' σp σp' U f g) (i : h.J) (W : Q.P.A.left.Opens) (hWU : W ≤ U) (hW : Y.q.left ⁻¹ᵁ W ≤ h.W i)
    {A : Type} [CommRing A] (π : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) →+* A)
    (hΘ : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0) :
    π ((Y.q.left.app W).hom (resG _ hWU g)) - 2 * (N : A) * π (h.d i _ ((Y.q.left.app W).hom (resG _ hWU f))) =
      2 * ∑ a, π (constFn Y.H.hom _ (h.u a)) * π (dd a _ ((Y.q.left.app W).hom (resG _ hWU f))) := by
  obtain ⟨τ, τp, t₁, t₂, a₁⟩ := h₁
  obtain ⟨τ', τp', t₃, t₄, a₂⟩ := h₂
  have hV := hW.trans (h.le i)
  have hWc : h.W i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) := Glue.le_wchart _ (h.le i)
  have hfn : ∀ y ∈ Y.q.left ⁻¹ᵁ W, ∀ x : Γ(Q.P.A.left, U),
      gs (𝟙 _) y (Y.q.left ⁻¹ᵁ W) ((Y.q.left.app W).hom (resG _ hWU x)) =
        (Y.q.left.stalkMap y).hom (gs (𝟙 _) (Y.q.left y) U x) := fun y hy x => by
    rw [gs_pull (𝟙 _) Y.q.left y W hy, Category.id_comp]
    exact (gs_res Y.q.left y hWU hy x).trans (gs_stalk _ y U (hWU hy) x)
  have act : ∀ {s s' : SecM Y.q.left Q.P.L N}, h.Acts N s s' → rsT (s'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) N _ (rsT (s.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) := fun {s s'} a => by
    have := congrArg (fun x => rsT x (Y.q.left ⁻¹ᵁ W)) (a i)
    simp only [rsT_op h hdd N i _ hW] at this
    exact (rsT_rsT hWc hW _).symm.trans (this.trans (congrArg _ (rsT_rsT hWc hW _)))
  have e₁ : rsT (τ.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, e σ τ t₁, e σ' τ' t₃, (hr _ (hWU hy) J' hJ').2, map_mul, _root_.mul_assoc]
  have e₂ : rsT (τp.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τp'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) +
      (Y.q.left.app W).hom (resG _ hWU g) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_add (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, hfn y hy, e σp τp t₂, e σ' τ' t₃, e σp' τp' t₄,
      hg _ (hWU hy) J' hJ', map_add, map_mul, map_mul]
    ring
  have hu : IsUnit (rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) :=
    Y.H.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (e σ' τ' t₃))).mpr
        (((hr _ (hWU hy) J' hJ').1.map _).mul c.isUnit)
  refine rem_eq h hdd N i _ hW π hΘ _ _ _ hu ?_
  rw [← e₁, ← act a₁, ← act a₂, e₂]

theorem rem_indep (hdd : ∀ a, IsField ⊤ (dd a)) (hB : IsBasic Y h) {K : Type} [Field K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W)) {D' : R → K}
    (hdl : LocDerK p Q.P.A.hom m D' ⊤ dl)
    (desc : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m →
      ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) =
        pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W)))
    (N₁ N₂ : ℕ) (β₁ β₂ : Q.X) (σ σ' σp σp' : Q.SecB N₁ β₁) (ρ ρ' ρp ρp' : Q.SecB N₂ β₂) (U : Q.P.A.left.Opens)
    (f g₁ g₂ : Γ(Q.P.A.left, U)) (r₁ : IsRatio Q σ σ' U f) (r₂ : IsRatio Q ρ ρ' U f)
    (h₁ : TActs Y h N₁ β₁ σ σp) (h₂ : TActs Y h N₁ β₁ σ' σp') (h₃ : TActs Y h N₂ β₂ ρ ρp) (h₄ : TActs Y h N₂ β₂ ρ' ρp')
    (e₁ : IsRem Q σ' σp σp' U f g₁) (e₂ : IsRem Q ρ' ρp ρp' U f g₂) :
    (m.app U).hom g₁ - 2 * (N₁ : Γ(Z, m ⁻¹ᵁ U)) * dl U f = (m.app U).hom g₂ - 2 * (N₂ : Γ(Z, m ⁻¹ᵁ U)) * dl U f := by
  have := Y.smooth_q
  have hs := (AbConst.surjective_q Y).1
  choose V hV using fun i => (hB i).1
  refine eq_of_rsT_eq (fun i => m ⁻¹ᵁ (U ⊓ V i)) (fun i => pre_mono m inf_le_left) (fun y hy => ?_) _ _ fun i => ?_
  · obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hx ▸ hi⟩
  obtain ⟨W, hWe⟩ : ∃ W, W = U ⊓ V i := ⟨_, rfl⟩
  have hWU : W ≤ U := hWe.le.trans inf_le_left
  have hW : Y.q.left ⁻¹ᵁ W ≤ h.W i := (pre_mono _ (hWe.le.trans inf_le_right)).trans (hV i).ge
  rw [← hWe]
  have red : ∀ (N : ℕ) (g : Γ(Q.P.A.left, U)), rsT ((m.app U).hom g - 2 * (N : Γ(Z, m ⁻¹ᵁ U)) * dl U f) (m ⁻¹ᵁ W) =
      (m.app W).hom (resG _ hWU g) - 2 * (N : Γ(Z, m ⁻¹ᵁ W)) * dl W (resG _ hWU f) := fun N g => by
    rw [hdl.res U W hWU le_top, rsT_of_le (pre_mono m hWU), rsT_of_le (pre_mono m hWU), map_sub, map_mul, map_mul,
      map_natCast, map_ofNat, res_app m hWU]
  rw [red, red]
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  have hΘ' : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0 := fun a b => by
    rw [hc, hΘ, constFn, map_zero, map_zero]
  have hd : ∀ x, (b.app _).hom (dl W x) = π (h.d i _ ((Y.q.left.app W).hom x)) := fun x => by
    have := desc _ a b w i W hW x
    rw [pbT, pbT, dif_pos le_rfl, dif_pos hle] at this
    rw [Scheme.Hom.app_eq_appLE b]
    exact this
  refine GlobalTheory.FunDescent.app_injective b _ ?_
  show (b.app _).hom _ = (b.app _).hom _
  simp only [map_sub, map_mul, map_natCast, map_ofNat, key, hd]
  exact (rem_chart Y h hdd N₁ β₁ σ σ' σp σp' U f g₁ r₁ h₁ h₂ e₁ i W hWU hW π hΘ').trans
    (rem_chart Y h hdd N₂ β₂ ρ ρ' ρp ρp' U f g₂ r₂ h₃ h₄ e₂ i W hWU hW π hΘ').symm

end Ray

theorem closed_fibre_rem_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (N₁ N₂ : ℕ), 1 ≤ N₁ → 1 ≤ N₂ → ∀ (β₁ β₂ : P.D.toPre.X) (σ σ' σp σp' : P.D.toPre.SecB N₁ β₁) (ρ₂ ρ₂' ρp ρp' : P.D.toPre.SecB N₂ β₂) (U : P.D.toPre.P.A.left.Opens) (f g₁ g₂ : Γ(P.D.toPre.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f → GlobalTheory.HeatRatio.IsRatio P.D.toPre ρ₂ ρ₂' U f → TActs Y h N₁ β₁ σ σp → TActs Y h N₁ β₁ σ' σp' → TActs Y h N₂ β₂ ρ₂ ρp → TActs Y h N₂ β₂ ρ₂' ρp' → GlobalTheory.HeatRatio.IsRem P.D.toPre σ' σp σp' U f g₁ → GlobalTheory.HeatRatio.IsRem P.D.toPre ρ₂' ρp ρp' U f g₂ → (m₀.app U).hom g₁ - 2 * (N₁ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - 2 * (N₂ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hdd D q _ h hB hΘ ρ hρ A₀ _ m₀ hm dl hdl desc N₁ N₂ _ _ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂
    r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  refine rem_indep Y h (fun a => (hdd a).1) hB ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) (fun a b => ?_) A₀.hom m₀
    hm.1.w dl hdl desc N₁ N₂ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂ r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
    by_contra hne
    exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
  show (ρ (h.Θ a b)).fst = 0
  simp [hρ, h0]

end GlobalTheory.HeatRatio.Closed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMulStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  first | exact @GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | exact GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | (intros; apply GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGe
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem colength_range_map_ge (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  obtain ⟨hfin, -⟩ := rigExt_field_of_charP p k hp G
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have hred : ∀ m : T.M H, T.red G (T.map q m) = rigExtMap q (T.red H m) := fun m => by
    show T.base.red G trivial (T.base.smap trivial trivial (SemiHom.ofHom q) m) = _
    rw [T.base.red_smap, SemiHom.ofHom_rig]
  constructor
  · haveI : Module.Finite k G.omega :=
      Module.Finite.of_injective G.rigOfOmega (G.rigOfOmega_injective_of_eq_zero hp)
    obtain ⟨-, hsurj, -, hsemi, hnat⟩ := hθ G
    let Q := LinearMap.range (omegaMap G H q)
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.omega ⧸ Q) (WittVector.frobeniusEquiv p k)
      (Q.mkQ.toAddMonoidHom.comp (θ G)) (Q.mkQ_surjective.comp hsurj) (fun a n => ?_)
      (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (θ G (WittVector.frobenius a • n)) = WittVector.constantCoeff a • Q.mkQ (θ G n)
      rw [hsemi, LinearMap.map_smul]
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (θ G (T.map q m)) = 0
      rw [hnat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
  · haveI : Module.Finite k G.dual.Lie := Module.Finite.of_surjective (G.rigToLie hp) (G.rigToLie_surjective hp)
    let Q := LinearMap.range (lieMap H.dual G.dual (dualHom G H q))
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.dual.Lie ⧸ Q) (RingEquiv.refl _)
      ((Q.mkQ ∘ₗ G.rigToLie hp).toAddMonoidHom.comp (T.red G).toAddMonoidHom)
      ((Q.mkQ_surjective.comp (G.rigToLie_surjective hp)).comp (T.base.red_surjective G trivial))
      (fun a n => ?_) (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (G.rigToLie hp (T.red G (a • n))) = WittVector.constantCoeff a • Q.mkQ (G.rigToLie hp (T.red G n))
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.map_smul]
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (G.rigToLie hp (T.red G (T.map q m))) = 0
      rw [hred, rigToLie_rigExtMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleRootsEvaluationInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_roots_evaluation_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.GTateGlue.glue) | (exact GlobalTheory.UPel.HT.GTateGlue.glue) | (intros; apply GlobalTheory.UPel.HT.GTateGlue.glue  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstK
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConstNZ

theorem constK : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.ConstK := by
  intro h1 h2 hLM h3 h4 h5
  obtain ⟨CF0, hH⟩ := ((GlobalTheory.T.big_theta_kernel_integrable h1 h2 h3 h4 h5).and (GlobalTheory.T.small_theta_kernel_translate_integrable h1 h2 h3 h4 h5)).and (GlobalTheory.T.exists_matched_flip_theta_integral h1 h2 hLM h3 h4 h5)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hb, hs⟩, hn⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t
  obtain ⟨M, hM, a, τ, τ', n, Φ, hnat, hfl, g, g₁, hI⟩ := hn i j t
  obtain ⟨b', hb'⟩ := ch.rm.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched ch.S.B t ch.rm i j (tensT ch.W a τ) (tensT ch.W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hfl, rfl, rfl⟩
  obtain ⟨z, hz, hzi⟩ := hs i j t M hM _ _ hΘ g g₁
  have hconv : SquareConv ch.W M _ _ z g g₁ := ⟨hb i j t M hM _ _ hΘ g g₁, hzi⟩
  have hc := hch.const i j t M hM _ _ hΘ z g g₁ hconv
  have hL : zdeg z * ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := mul_ne_zero hz hI
  rw [hc] at hL
  exact ⟨⟨M, hM, _, _, hΘ, z, g, g₁, hconv, right_ne_zero_of_mul hL⟩, left_ne_zero_of_mul hL⟩

end GlobalTheory.ConstNZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCo
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isSeparated_left_of_isAbelianScheme {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have h1 : IsProper A.hom := h.proper
  have h2 : IsSeparated A.hom := inferInstance
  rw [Scheme.isSeparated_iff, ← terminal.comp_from A.hom]
  infer_instance

theorem pTaylor : PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ hφ₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP₀ D _ _ π κ hκ hπ N t ht htN
    j hj A' _ φ' _ m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g hφ₀ hA hg
  have hspan := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hmem : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨n, f, v, hv⟩ := Submodule.mem_span_set'.1 hmem
  choose a ha using fun r : Fin n ↦ (v r).2
  have hsum : (liftMor κ h).pull (m'.pull c) = ∑ r, f r • k.pull (a r) := by
    rw [← hv]; exact Finset.sum_congr rfl fun r _ ↦ by rw [ha]
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  have M := (m'.comp (liftMor κ h)).isMor
  have nn : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    rw [RingHom.id_comp, hi] at M
    exact M
  have hpull : nn.pull1 c.1 = ∑ r ∈ Finset.univ, f r • k.isMor.pull1 (a r).1 := by
    have e1 := IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor nn (fun _ ↦ rfl) hi c.1
    have e2 := congrArg (Submodule.subtype _) hsum
    rw [map_sum] at e2
    exact e1.symm.trans e2
  have key := GlobalTheory.T.taylor_period_eq_period_over_thickening_alt (F := F) (F₀ := fibFam u₀) e (fibUnif u₀)
    (isSeparated_left_of_isAbelianScheme 𝒜 hA) (isSeparated_left_of_isAbelianScheme A₀ hA₀) h0
    (fun _ ↦ trivial) (fun l _ ↦ (hτ l).symm) φ₀ (fun p ↦ (hE p.2).symm) πa (GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal κ hκ) κ
    (fun _ hd ↦ hd) N t ht htN (j : B →+* D) hj (A₀.hom ≫ spMap π)
    (by rw [Category.comp_id]; rfl) nn _ k.isMor rfl c.1 per hper Finset.univ f (fun r ↦ (a r).1)
    (fun r l ↦ P₀ l (a r)) _ (fun _ _ ↦ rfl) (fun r ↦ hP₀ (a r)) hpull x
  rw [crysToDR_apply, hsum, map_sum, ← key]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, hd (a r), smul_eq_mul]

end GlobalTheory.AnPer
end

