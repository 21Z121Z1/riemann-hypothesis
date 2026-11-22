import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3372
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularBaseRankTwoMetricFamily
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem core_exists : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (onLine d a b - onBase d a b) = Ψ (G (d + 1) a b) := by
  intro hC
  obtain ⟨G, hG, hAn⟩ := GlobalTheory.T.flag_bundle_pullback_height_compare hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H flB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨K, hKh, hK⟩ := GlobalTheory.T.homogeneous_line_base_difference d a b
  have hF : onLine d a b - onBase d a b = (X 4 - X 0) * ((X 3 - X 0) * K) := by rw [hK]; ring
  have hFv : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) ((X 3 - X 0) * K) = 0 := by
    simp
  have hFh : ((X 3 - X 0) * K : MvPolynomial (Fin 5) ℝ).IsHomogeneous (d + 1) := by
    have h1 : (X 3 - X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
      (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
    simpa [add_comm] using h1.mul hKh
  obtain ⟨r, hr, hsupp, hnorm⟩ := GlobalTheory.T.rank_two_flag_rational_sections k B Y q p d hq hp hreg π w E h H flB fl hfl A
  obtain ⟨s, c, hpol⟩ := GlobalTheory.T.homogeneous_form_powers_linear (d + 1) _ hFh
  rw [hF, GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A Φ hΦ r hr hsupp _ hFv s c hpol]
  exact hAn k B Y q p d hq hp hreg π w E h H flB fl hfl A Ψ hΨ r hr hnorm a b _ hF.symm s c hpol

end GlobalTheory.CovTest.SwapLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens)

def IsCoc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')

def CechFG (R : Type) [CommRing R] (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) : Prop :=
  ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, IsCoc W (e k)) ∧
    ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (r : Fin N → R) (h : ∀ i : J, Γ(Z, W i)),
      ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') + ∑ k, act i i' (r k) * e k i i'

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

def fv (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) : Γ(Z, B.1) :=
  f (Opposite.op A) (Opposite.op B) (homOfLE h).op

def gv (g : C0 (OAff s)) (A : Z.affineOpens) : Γ(Z, A.1) := g (Opposite.op A)

theorem fv_d0 (g : C0 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (d0 (OAff s) g) h = gv s g B - resG Z h (gv s g A) := rfl

theorem fv_add (f f' : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (f + f') h = fv s f h + fv s f' h := rfl

theorem fv_smul (r : R) (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (r • f) h = (secMap s B.1).hom r * fv s f h := rfl

theorem res_val (f : Z1 (OAff s)) {A B C : Z.affineOpens} (hBA : B.1 ≤ A.1) (hCB : C.1 ≤ B.1) :
    resG Z hCB (fv s f.1 hBA) = fv s f.1 (hCB.trans hBA) - fv s f.1 (A := B) hCB :=
  eq_sub_of_add_eq (f.2 (homOfLE hBA).op (homOfLE hCB).op).symm

variable (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))

def rho (f : C1 (OAff s)) (i i' : J) : Γ(Z, W i ⊓ W i') :=
  fv s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
    fv s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right

theorem rho_isCoc (hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (f : Z1 (OAff s)) :
    IsCoc W (rho W s hW hW2 f.1) := by
  intro i i' i''
  let T : Z.affineOpens := ⟨W i ⊓ W i' ⊓ W i'', hW3 i i' i''⟩
  have h1 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_left inf_le_left
  have h2 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_right inf_le_left
  have h3 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h4 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h5 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have h6 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  simp only [rho, map_sub]
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem rho_add (f f' : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (f + f') i i' = rho W s hW hW2 f i i' + rho W s hW hW2 f' i i' := by
  simp only [rho, fv_add]
  ring

theorem rho_smul (r : R) (f : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (r • f) i i' = (secMap s (W i ⊓ W i')).hom r * rho W s hW hW2 f i i' := by
  simp only [rho, fv_smul]
  ring

theorem rho_zero (i i' : J) : rho W s hW hW2 0 i i' = 0 := sub_self (0 : Γ(Z, W i ⊓ W i'))

theorem rho_sum {N : ℕ} (r : Fin N → R) (f : Fin N → C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (∑ k, r k • f k) i i' = ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * rho W s hW hW2 (f k) i i' := by
  induction N with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact rho_zero W s hW hW2 i i'
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, rho_add, rho_smul, ih]

theorem rho_d0 (g : C0 (OAff s)) (i i' : J) :
    rho W s hW hW2 (d0 (OAff s) g) i i' =
      resG Z inf_le_left (-gv s g ⟨W i, hW i⟩) - resG Z inf_le_right (-gv s g ⟨W i', hW i'⟩) := by
  simp only [rho, fv_d0, map_neg]
  ring

end GlobalTheory.CechFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem bracket_symbol_rescale_twist : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  intro Ω _ _ n δ₀ δL Λ q b c k hq
  have hpow : ∀ (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      d (q ^ k * x) = q ^ k * (d x + (k : FractionRing Ω) * x * (d q / q)) := by
    intro d x
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      field_simp
      ring
  have hbr : ∀ d : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (q ^ k * b) * d (q ^ k * c) - (q ^ k * c) * d (q ^ k * b)
        = q ^ k * q ^ k * (b * d c - c * d b) := by
    intro d
    rw [hpow d b, hpow d c]
    ring
  have h3 : q ^ (3 * k) = q ^ k * q ^ k * q ^ k := by ring
  simp only [hbr]
  simp only [hpow _ b]
  have hs : ∑ a, ∑ e, Λ a e * (q ^ k * (δL a b + (k : FractionRing Ω) * b * (δL a q / q))) *
        (q ^ k * q ^ k * (b * δL e c - c * δL e b))
      = q ^ k * q ^ k * q ^ k * ((k : FractionRing Ω) * b *
          (b * (∑ a, ∑ e, Λ a e * δL a q / q * δL e c)
            - c * (∑ a, ∑ e, Λ a e * δL a q / q * δL e b))
          + ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs, h3]
  ring

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecValLC

theorem valR_def' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := by
  unfold valR; rw [dif_pos h]

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_def' x U h, map_mul]

theorem valR_map' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_def' x V h, valR_def' x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]

theorem valR_id_app {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) (f : Γ(X, U)) :
    valR x ((𝟙 X) ⁻¹ᵁ U) ((Scheme.Hom.app (𝟙 X) U).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h
  rw [valR_def' x _ h, valR_def' x U hU]
  congr 1

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_def' x U h, map_pow]

theorem secM_valR_transition : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  intro X L k σ F _ ξ j j' hj hj'
  set LC := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k:ℤ)) with hLC
  have hW : ∀ i : L.ι, L.U i ≤ LC.U (fun _ => i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have h1 : ⊤ ≤ ξ ⁻¹ᵁ (LC.U (fun _ => j) ⊓ LC.U (fun _ => j')) := by
    intro x hx
    exact ⟨hW j (hj hx), hW j' (hj' hx)⟩
  have h2 : ⊤ ≤ ξ ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j')) := fun x hx => ⟨hj hx, hj' hx⟩
  have hle : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ (𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
  have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
      Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) =
      (X.presheaf.map (homOfLE hle).op).hom ((Scheme.Hom.app (𝟙 X) (L.U j ⊓ L.U j')).hom
        (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k := by
    show Units.val (∏ _i : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (k:ℤ)) = _
    rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  have hc := σ.compat (fun _ => j) (fun _ => j')
  have := congrArg (valR ξ _) hc
  rw [valR_map' _ _ h1, valR_mul' _ _ h1, valR_map' _ _ h1] at this
  rw [this, hg, valR_pow' _ _ h1, valR_map' _ _ h1, valR_id_app _ _ h2]

end GlobalTheory.SecValLC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueInFrameLinearCombinationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValueInFrame_linearCombination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  first | exact @GlobalTheory.Heat.exists_isValue_lin | exact GlobalTheory.Heat.exists_isValue_lin | (intros; apply GlobalTheory.Heat.exists_isValue_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
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

namespace GlobalTheory

namespace LocRegDesc

theorem exists_unit_mul_eq_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    (ρ : A →+* R) (hρ : ρ.Flat) (s b : A) (r : R) (hs : ρ s = ρ b * r) :
    ∃ g a : A, IsUnit (ρ g) ∧ g * s = b * a := by
  letI := ρ.toAlgebra
  haveI : Module.Flat A R := hρ
  have hrel : ∑ i, (![s, -b] : Fin 2 → A) i • (![1, r] : Fin 2 → R) i = 0 := by
    simp [Fin.sum_univ_two, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hs]
  have ht : Module.IsTrivialRelation (![s, -b] : Fin 2 → A) (![1, r] : Fin 2 → R) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, a, y, hx, hf⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ρ (a 0 j)) := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have := hx 0
      simp only [Matrix.cons_val_zero] at this
      rw [this]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hne j))
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨a 0 j, a 1 j, hj, ?_⟩
  have := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linear_combination this

end LocRegDesc

namespace LocRegDesc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill_on_basicOpen (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0)
    (f : Γ(X, U.1)) (hf : X.basicOpen f ≤ W) :
    ∃ g, IsUnit (ρ g) ∧
      (X.presheaf.map (homOfLE hf).op).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0 := by
  haveI hloc := U.2.isLocalization_basicOpen f
  set δV := (X.presheaf.map (homOfLE hf).op).hom δ with hδV
  set hV := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom h with hhV
  have key : X.basicOpen hV = X.basicOpen f ⊓ X.basicOpen h := Scheme.basicOpen_res _ _ _
  have hB : X.basicOpen hV ≤ X.basicOpen h := key ▸ inf_le_right
  have hzero : (X.presheaf.map (homOfLE (X.basicOpen_le hV)).op).hom δV = 0 := by
    rw [hδV, res_res, ← res_res hh hB, hδ, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U.2.basicOpen f).isCompact δV hV hzero
  obtain ⟨⟨e, m⟩, hem⟩ := IsLocalization.surj (Submonoid.powers f) δV
  simp only at hem
  have h0 : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (h ^ n * e) = 0 := by
    rw [map_mul, ← hem, map_pow]
    change hV ^ n * (δV * _) = 0
    rw [← _root_.mul_assoc, hn, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
  simp only at hj
  have hc : ρ (f ^ j * e) = 0 := by
    have : ρ h ^ n * ρ (f ^ j * e) = 0 := by
      rw [← map_pow, ← map_mul, show h ^ n * (f ^ j * e) = f ^ j * (h ^ n * e) by ring, hj, map_zero]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hρh)
  obtain ⟨g, a, hu, hg⟩ := exists_unit_mul_eq_of_flat ρ hρ (f ^ j * e) 0 0 (by simp [hc])
  refine ⟨g, hu, ?_⟩
  rw [map_mul, res_res]
  change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * δV = 0
  have u1 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (m : Γ(X, U.1))) :=
    IsLocalization.map_units _ m
  have u2 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (f ^ j)) :=
    IsLocalization.map_units _ (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)
  rw [← u1.mul_left_eq_zero, ← u2.mul_left_eq_zero, _root_.mul_assoc _ δV, hem, ← map_mul, ← map_mul,
    show g * e * f ^ j = g * (f ^ j * e) by ring, hg, zero_mul, map_zero]

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0) :
    ∃ g, IsUnit (ρ g) ∧ (X.presheaf.map (homOfLE hWU).op).hom g * δ = 0 := by
  let p : Set X → Prop := fun t => ∃ g, IsUnit (ρ g) ∧ ∀ y (hy : y ∈ W), y ∈ t →
    (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0
  have hp : p (W : Set X) := by
    refine hW.induction_on ?_ ?_ ?_ ?_
    · exact ⟨1, by simp, fun y _ hy => hy.elim⟩
    · rintro s t hst ⟨g, hg, H⟩
      exact ⟨g, hg, fun y hy hs => H y hy (hst hs)⟩
    · rintro s t ⟨g₁, hg₁, H₁⟩ ⟨g₂, hg₂, H₂⟩
      refine ⟨g₁ * g₂, by rw [map_mul]; exact hg₁.mul hg₂, fun y hy hyst => ?_⟩
      rw [map_mul (X.presheaf.map (homOfLE hWU).op).hom g₁ g₂]
      rcases hyst with hs | ht
      · rw [mul_right_comm, map_mul (X.presheaf.germ W y hy).hom, H₁ y hy hs, zero_mul]
      · rw [_root_.mul_assoc, map_mul (X.presheaf.germ W y hy).hom, H₂ y hy ht, mul_zero]
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      obtain ⟨g, hg, H⟩ := exists_unit_kill_on_basicOpen X U W hWU R ρ hρ h hh hρh δ hδ f hf
      refine ⟨X.basicOpen f, mem_nhdsWithin_of_mem_nhds ((X.basicOpen f).isOpen.mem_nhds hxf),
        g, hg, fun y hy hyf => ?_⟩
      rw [← X.presheaf.germ_res_apply (homOfLE hf) y hyf, H, map_zero]
  obtain ⟨g, hg, H⟩ := hp
  refine ⟨g, hg, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf W _ 0 fun y hy => ?_
  exact (H y hy hy).trans (map_zero (X.presheaf.germ W y hy).hom).symm

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_one (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (θ : Γ(X, W))
    (H : ∀ (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) *
        (X.presheaf.map (homOfLE hh).op).hom θ → ρ h ^ N ∣ ρ s) :
    ∃ g, IsUnit (ρ g) ∧ ∃ s : Γ(X, U.1),
      (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ := by
  haveI hloc := U.2.isLocalization_basicOpen h
  obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hsm⟩ :=
    IsLocalization.surj (Submonoid.powers h) ((X.presheaf.map (homOfLE hh).op).hom θ)
  simp only at hsm
  obtain ⟨r, hr⟩ := H s N (by
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) s =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) * _
    rw [← hsm, mul_comm])
  obtain ⟨g₁, a, hu₁, hga⟩ := exists_unit_mul_eq_of_flat ρ hρ s (h ^ N) r (by rw [map_pow, hr])
  set δ := (X.presheaf.map (homOfLE hWU).op).hom a - (X.presheaf.map (homOfLE hWU).op).hom g₁ * θ
    with hδdef
  have hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0 := by
    have u : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N)) :=
      IsLocalization.map_units _ (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
    rw [← u.mul_left_eq_zero, hδdef, map_sub, map_mul, res_res, res_res]
    change (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) a - algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) g₁ *
      (X.presheaf.map (homOfLE hh).op).hom θ) * algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) = 0
    rw [sub_mul, _root_.mul_assoc, hsm, ← map_mul, ← map_mul, hga, mul_comm a, sub_self]
  obtain ⟨g₂, hu₂, hk⟩ := exists_unit_kill X U W hWU hW R ρ hρ h hh hρh δ hδ
  refine ⟨g₂ * g₁, by rw [map_mul]; exact hu₂.mul hu₁, g₂ * a, ?_⟩
  rw [map_mul, map_mul]
  rw [hδdef] at hk
  linear_combination hk

end LocRegDesc

theorem LocRegDesc.descent : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  intro X U W hWU hW R _ _ _ ρ hρ mm hmm h hh hρh J _ θ H
  choose g hg s hs using fun i => LocRegDesc.exists_unit_one X U W hWU hW R ρ hρ h hh hρh (θ i) (H i)
  haveI := Fintype.ofFinite J
  classical
  refine ⟨∏ i, g i, ?_, fun i => ⟨s i * ∏ j ∈ Finset.univ.erase i, g j, ?_⟩⟩
  · rw [← hmm, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hg i)
  · rw [map_mul, hs i, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), map_mul]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIsoStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'), (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x = ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  first | exact @GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | exact GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | (intros; apply GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage <;> assumption)
end

