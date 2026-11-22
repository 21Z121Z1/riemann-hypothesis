import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0200
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

noncomputable def galSpecHom (τ : Ω ≃ₐ[K] Ω) :
    Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact τ.commutes c)

theorem galSpecHom_one : galSpecHom (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

theorem galSpecHom_mul (τ τ' : Ω ≃ₐ[K] Ω) :
    galSpecHom (τ * τ') = galSpecHom τ ≫ galSpecHom τ' := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

noncomputable def galPointAct (A : Over (Sp K)) [MonObj A] :
    (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ A) where
  toFun τ :=
    { toFun := fun x => galSpecHom τ ≫ x
      invFun := fun x => galSpecHom τ⁻¹ ≫ x
      left_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, inv_mul_cancel, galSpecHom_one,
          Category.id_comp]
      right_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, mul_inv_cancel, galSpecHom_one,
          Category.id_comp]
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  map_one' := by
    ext1 x
    change galSpecHom 1 ≫ x = x
    rw [galSpecHom_one, Category.id_comp]
  map_mul' τ τ' := by
    ext1 x
    change galSpecHom (τ * τ') ≫ x = galSpecHom τ ≫ galSpecHom τ' ≫ x
    rw [galSpecHom_mul, Category.assoc]

theorem galPointAct_left (A : Over (Sp K)) [MonObj A] (τ : Ω ≃ₐ[K] Ω)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) :
    (galPointAct A τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left := rfl

theorem galPointAct_eq_of_agree (A : Over (Sp K)) [MonObj A] (L : IntermediateField K Ω)
    (τ τ' : Ω ≃ₐ[K] Ω) (h : ∀ c ∈ L, τ c = τ' c) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A)
    (y : Sp L ⟶ A.left) (hy : spMap (algebraMap L Ω) ≫ y = x.left) :
    galPointAct A τ x = galPointAct A τ' x := by
  ext1
  rw [galPointAct_left, galPointAct_left, ← hy, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact h c c.2

theorem algEquiv_mem_of_normal (L : IntermediateField K Ω) [Normal K L] (τ : Ω ≃ₐ[K] Ω)
    {c : Ω} (hc : c ∈ L) : τ c ∈ L := by
  have := AlgEquiv.restrictNormal_commutes τ L ⟨c, hc⟩
  change ((τ.restrictNormal L ⟨c, hc⟩ : L) : Ω) = τ c at this
  rw [← this]
  exact Subtype.prop _

theorem pow_tame_relation (L : IntermediateField K Ω) [Normal K L] (σ φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ c ∈ L, φ (σ c) = (σ ^ q) (φ c)) (N : ℕ) :
    ∀ c ∈ L, (φ ^ N * σ) c = (σ ^ q ^ N * φ ^ N) c := by
  have h1 : ∀ (a : ℕ), ∀ c ∈ L, φ ((σ ^ a) c) = (σ ^ (q * a)) (φ c) := by
    intro a
    induction a with
    | zero => intro c _; simp
    | succ a ih =>
      intro c hc
      rw [pow_succ', AlgEquiv.mul_apply, h _ (algEquiv_mem_of_normal L _ hc), ih c hc,
        ← AlgEquiv.mul_apply, ← pow_add, Nat.mul_succ, Nat.add_comm]
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
    intro c hc
    have := ih c hc
    simp only [AlgEquiv.mul_apply] at this
    rw [pow_succ' φ, pow_succ' q]
    simp only [AlgEquiv.mul_apply]
    rw [this, h1 _ _ (algEquiv_mem_of_normal L _ hc)]

end

theorem galois_action_torsion_points : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  intro K _ _ P Ω _ _ _ l q hl hrat σ φ K' _ j hζ hL
  obtain ⟨-, ⟨e, he, hgal⟩, hfield⟩ := GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl
  have hφ : ∀ (m N : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → (φ ^ N) ζ = ζ ^ q ^ N := by
    intro m N ζ h
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (hζ m ζ h).2, ← pow_mul, pow_succ']
  refine ⟨e, galPointAct P.A, fun τ x => rfl, he, ?_, ?_, ?_⟩
  · intro N n x y hx hy
    obtain ⟨h1, h2⟩ := hgal σ n x y _ _ hx hy (galPointAct_left _ σ x) (galPointAct_left _ σ y)
    obtain ⟨-, h3⟩ := hgal (φ ^ N) n x y _ _ hx hy (galPointAct_left _ _ x)
      (galPointAct_left _ _ y)
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · rw [h2, (hζ n _ h1).1]
    · rw [h3, hφ n N _ h1, Units.val_pow_eq_pow_val]
  · intro N n x hx
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨y, hy⟩ := hpts x hx
    have := galPointAct_eq_of_agree P.A L _ _
      (pow_tame_relation L σ φ q (fun c hc => (hL L hfin hnorm hp c hc).1) N) x y hy
    rw [map_mul, map_mul, map_pow (galPointAct P.A) σ] at this
    rw [← MulAut.mul_apply, this, MulAut.mul_apply]
    generalize galPointAct P.A (φ ^ N) x = z
    generalize q ^ N = k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  · intro n x hx hfix
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨E, hE1, hE2, -⟩ := exists_fieldOfValues P.A.left Ω x.left
    have hEL := (hE2 L (algebraMap L Ω)).2 (hpts x hx)
    have hσ := (hE1 σ.toRingEquiv.toRingHom (RingHom.id Ω)).1 (by
      rw [← galPointAct_left, hfix]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ x.left) (Spec.map_id _).symm))
    refine (hE2 K' j).1 fun c hc => ?_
    obtain ⟨d, rfl⟩ := hEL hc
    exact (hL L hfin hnorm hp _ d.2).2 (hσ _ hc)

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExistStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_torsionLabels_exist : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → Nonempty u.Lab := by
  first | exact @GlobalTheory.ZH.labels_exist | exact GlobalTheory.ZH.labels_exist | (intros; apply GlobalTheory.ZH.labels_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem le_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (h : x (IsLocalRing.closedPoint A) ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge

theorem isUnit_valR {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (x : Sp A ⟶ X)
    {k : H.ι} (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) (h : x (IsLocalRing.closedPoint A) ∈ nonzeroLocus s) :
    IsUnit (valR x _ (s.f k)) := by
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff x _ _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s x _ (hk trivial)).1 h)
  exact (GlobalTheory.Points.le_preimage_basicOpen_iff x hk _).1 (le_of_closedPoint x h₁)

theorem grpPullback (u : ρ.UTest p y₀) : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK)
    (u.U.gen.hom.left ≫ u.φ) :=
  haveI := u.U.gen_hom
  ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl

theorem lbIso (u : ρ.UTest p y₀) : LBIso (u.U.LG.L.pull (pullback.fst u.G.hom (jK u.V)))
    (ρ.P.L.pull (u.U.gen.hom.left ≫ u.φ)) :=
  LBIso.trans (pull_isLB u.U.LG.isLB _) (pull_isLB u.A.isLB _) (pull_isLB ρ.P.isLB _) (LBIso.symm u.U.ext)
    (u.lb.chartPull (Geo.Tor.chartPullPull u.A.L _ _ rfl)
      (chartPullSame ρ.P.L (K := PUnit) (fun _ => u.U.gen.hom.left ≫ u.φ) (fun _ => u.φ) (fun _ => 1) _ fun _ => rfl))

theorem norm_le (u : ρ.UTest p y₀) (v : u.V) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) v)‖ ≤ 1 :=
  (u.norm_le _).2 ⟨v, rfl⟩

theorem norm_unit (u : ρ.UTest p y₀) {v : u.V} (hv : IsUnit v) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) v)‖ = 1 := by
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  have h₁ := norm_le u v
  have h₂ := norm_le u w
  have h₃ : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) v)‖ *
      ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) w)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, hw, map_one, map_one, norm_one]
  nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) v)),
    norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) w))]

theorem exists_section (hL : Laws2) (u : ρ.UTest p y₀) : ∃ (ϑ : H0 u.U.LG.L 1) (c : ℝ), 0 < c ∧
    (∃ z ∈ nonzeroLocus ϑ, u.G.hom z = IsLocalRing.closedPoint u.V) ∧ ∀ a h, Extends u a h →
      ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ c ∧
        (h.left (IsLocalRing.closedPoint u.V) ∈ nonzeroLocus ϑ → ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = c) := by
  obtain ⟨w, hw⟩ := lbIso u
  obtain ⟨θ, hθ, hval⟩ := GlobalTheory.T.exists_section_of_baseProduct_section S.R ρ.P ρ.th₁
  obtain ⟨ϑ, c, hc, hϑ, hrel⟩ := GlobalTheory.T.exists_primitive_scaling_alt u.V u.G u.semi u.U.LG.L u.U.LG.isLB _ ρ.P.L ρ.P.isLB _ w hw θ (by
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.exists_mem_nonzeroLocus_fibre_of_secBasis hL.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
      (spMap u.yK (IsLocalRing.closedPoint _))
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (grpPullback u).1 _ _ e
    exact ⟨z, by rw [hz]; exact hθ y hy⟩)
  obtain ⟨lam, hlam, hfr⟩ := GlobalTheory.T.torsionFrame_pow_eq_integral_generator u.V u.G u.semi u.U.LG _ ρ.P ρ.rig ρ.rig_gen _ _ (grpPullback u) w hw (S.r * S.N)
  set e := algebraMap (FractionRing u.V) (PadicAlgCl p) with he
  have pos : ∀ x : FractionRing u.V, x ≠ 0 → 0 < ‖e x‖ := fun x hx =>
    norm_pos_iff.2 ((map_ne_zero e).2 hx)
  refine ⟨ϑ, (‖e c‖ * ‖e lam‖)⁻¹, inv_pos.2 (mul_pos (pos c hc) (pos lam hlam)), hϑ, ?_⟩
  rintro a h ⟨x, x₁, x₂, x₃⟩
  obtain ⟨i, hi⟩ := exists_chart u.U.LG.isLB (h.left (IsLocalRing.closedPoint u.V))
  obtain ⟨k, hk⟩ := exists_chart ρ.P.isLB ((x ≫ u.U.gen.hom.left ≫ u.φ) (IsLocalRing.closedPoint _))
  have hi' := le_of_closedPoint h.left hi
  have hk' := le_of_closedPoint _ hk
  have hi₂ : ⊤ ≤ (show Sp u.V ⟶ u.G.left from h.left) ⁻¹ᵁ
      LB.wchart u.U.LG.L (fun _ : Fin 1 => 𝟙 u.G.left) (fun _ => i) :=
    fun z _ => Set.mem_iInter.2 fun _ => hi' (x := z) trivial
  have e₁ := hrel x x₂ i k (by rw [x₁]; exact fun z _ => hi' (x := jK u.V z) trivial) hk'
  obtain ⟨v, e₂⟩ := hfr _ _ (ρ.fr_tors a) h x x₁ x₂ x₃ i k hi' hk'
  have e₃ := hval _ _ _ (ρ.th_val a) _ u.yK k (by rw [← x₃]; exact hk')
  have e₄ : valR (x ≫ pullback.fst u.G.hom (jK u.V)) _ (ϑ.f fun _ => i) = algebraMap u.V (FractionRing u.V)
      (valR (show Sp u.V ⟶ u.G.left from h.left) _ (ϑ.f fun _ => i)) := by
    rw [x₁]
    exact GlobalTheory.HolHom.valR_spMap _ _ _ hi₂ _
  have hω : valR x _ (w.s (fun _ => k, fun _ => i)).val ≠ 0 := by
    have : ⊤ ≤ x ⁻¹ᵁ ((ρ.P.L.pull (u.U.gen.hom.left ≫ u.φ)).U (fun _ => k) ⊓
        (u.U.LG.L.pull (pullback.fst u.G.hom (jK u.V))).U (fun _ => i)) := fun z _ =>
      ⟨mem_pull.2 (hk' (x := z) trivial), mem_pull.2 (by
        have : (x ≫ pullback.fst u.G.hom (jK u.V)) z ∈ u.U.LG.L.U i := by rw [x₁]; exact hi' (x := jK u.V z) trivial
        exact this)⟩
    exact (GlobalTheory.HolHom.valR_eq x _ this _).trans_ne ((Units.isUnit _).map _).ne_zero
  rw [e₄, x₃, e₃] at e₁
  have hy : y₀ ⟨S.th a, S.th_mem a⟩ = e (u.yK ⟨S.th a, S.th_mem a⟩) := (RingHom.congr_fun u.fac _).symm
  rw [hy]
  generalize valR x _ (w.s (fun _ => k, fun _ => i)).val = ω at e₁ e₂ hω
  generalize valR (X := (baseOver (Sp S.R)).left) (spMap u.yK) _ ((ρ.fr a).s fun _ => k).val = τ at e₁ e₂
  have hn : (S.r * S.N) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have n₂ : ‖e τ‖ = ‖e lam‖ * ‖e ω‖ := by
    have := congrArg (fun t => ‖e t‖) e₂
    simp only [map_mul, map_pow, norm_mul, norm_pow] at this
    rw [norm_unit u v.isUnit, _root_.mul_one] at this
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) hn).1 this
  have n₁ := congrArg (fun t => ‖e t‖) e₁
  simp only [map_mul, norm_mul, n₂] at n₁
  have n₃ : ‖e (u.yK ⟨S.th a, S.th_mem a⟩)‖ = (‖e c‖ * ‖e lam‖)⁻¹ * ‖e (algebraMap u.V (FractionRing u.V)
      (valR (show Sp u.V ⟶ u.G.left from h.left) _ (ϑ.f fun _ => i)))‖ := by
    have := pos c hc; have := pos lam hlam; have := pos ω hω
    field_simp
    apply mul_left_cancel₀ (pos ω hω).ne'
    linarith
  rw [n₃]
  refine ⟨mul_le_of_le_one_right (by positivity) (norm_le u _), fun H => ?_⟩
  rw [norm_unit u (isUnit_valR ϑ _ hi₂ H), _root_.mul_one]

theorem exists_translate (hL : Laws) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (IsLocalRing.maximalIdeal V)} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G]
    [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1)
    (hϑ : ∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) {κ : Type} [Field κ] [IsAlgClosed κ]
    (f : V →+* κ) (hf : IsLocalHom f) {n : ℕ} (hn : 2 ≤ n) (hκ : (n : κ) ≠ 0) (c : Over.mk (spMap f) ⟶ G) :
    ∃ x : Over.mk (spMap f) ⟶ G, x ^ n = 1 ∧ (c * x).left (IsLocalRing.closedPoint κ) ∈ nonzeroLocus ϑ := by
  have := U.smooth
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_thetaSection_nonzeroLocus_specialFibre_iff hL.globalFns V D A G U ϑ
  obtain ⟨π, hπ, hlift⟩ := GlobalTheory.T.exists_specialFibre_projection_abelianPart V D.toPre G (U.gt 0) κ f hf
  obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.exists_good_torsion_translate_of_section hL.polBaseChange hL.goodPt _ D.toPre.P θ κ (spMap f) n hn hκ (by
    obtain ⟨z, hz, e⟩ := hϑ
    have hm : IsLocalRing.maximalIdeal V ^ (0 + 1) = IsLocalRing.maximalIdeal V := pow_one _
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 (by rw [hm]; exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
    have hcl : ∀ s : Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)),
        thick V (IsLocalRing.maximalIdeal V) 0 s = IsLocalRing.closedPoint V := fun s =>
      PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime _)) fun a ha => by
          show Ideal.Quotient.mk _ a ∈ s.asIdeal
          rw [Ideal.Quotient.eq_zero_iff_mem.2 (hm.ge ha)]
          exact zero_mem _).symm
    obtain ⟨s⟩ : Nonempty (Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) z s (e.trans (hcl s).symm)
    refine ⟨_, (hθ y).1 (by
      show pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y ∈ _
      rw [hy]; exact hz), IsLocalRing.closedPoint κ, ?_⟩
    exact (IsLocalRing.comap_closedPoint f).trans ((hcl _).symm.trans
      (congrArg (fun g => g y) (Over.w (U.gt 0).pG)).symm)) (π c)
  obtain ⟨x, hx, rfl⟩ := hlift n (by omega) b hb
  obtain ⟨y, y₁, y₂⟩ := hπ (c * x)
  refine ⟨x, hx, ?_⟩
  rw [← y₁]
  refine (hθ _).2 ?_
  have := hb' (x := IsLocalRing.closedPoint κ) trivial
  rw [← map_mul, ← y₂] at this
  exact this

theorem isUnit_level (u : ρ.UTest p y₀) (hy : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    IsUnit ((S.r * S.N : ℕ) : u.V) := by
  obtain ⟨a, ha⟩ := S.unit.exists_right_inv
  obtain ⟨v, hv⟩ := (u.norm_le (u.yK (algebraMap o S.R a))).1 ((congrArg _ (RingHom.congr_fun u.fac _)).trans_le (hy a))
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, map_natCast, map_one, ← map_natCast (u.yK.comp (algebraMap o S.R))]
  exact (map_mul (u.yK.comp (algebraMap o S.R)) _ _).symm.trans (by rw [ha, map_one])

theorem eq_zero_of_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {w : X} (hw : q w ≤ 0) : w = 0 := by
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • w := smul_left_injective ℤ h
  have hfin : {x | ¬ (1 : ℝ) ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 1)
  refine Set.infinite_range_of_injective hinj (hfin.subset ?_)
  rintro _ ⟨k, rfl⟩
  show ¬ 1 ≤ q (k • w)
  rw [q.map_smul, zsmul_eq_mul]
  push_cast
  nlinarith [mul_self_nonneg (k : ℝ)]

theorem exists_bound (hL : Laws) (hL₂ : Laws2) (u : ρ.UTest p y₀) (hy : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ S.r * S.N) : ∃ c : ℝ, 0 < c ∧ ∀ a, u.Integral a →
      ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ c ∧ ∃ b, n • b = 0 ∧ ‖y₀ ⟨S.th (a + b), S.th_mem (a + b)⟩‖ = c := by
  obtain ⟨ϑ, c, hc, hϑ, H⟩ := exists_section hL₂ u
  refine ⟨c, hc, fun a ha => ?_⟩
  obtain ⟨h, hh⟩ := (integral_iff u a).1 ha
  refine ⟨(H a h hh).1, ?_⟩
  have := u.U.smooth
  have := u.U.separated
  have hu : IsUnit (n : u.V) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (isUnit_level u hy)
  let κ := AlgebraicClosure (IsLocalRing.ResidueField u.V)
  let f : u.V →+* κ := (algebraMap (IsLocalRing.ResidueField u.V) κ).comp (IsLocalRing.residue u.V)
  have hf : IsLocalHom f := inferInstance
  let r : Over.mk (spMap f) ⟶ baseOver (Sp u.V) := Over.homMk (spMap f) (Category.comp_id _)
  obtain ⟨x, hx, hx'⟩ := exists_translate hL u.U ϑ hϑ f hf hn
    (by rw [← map_natCast f]; exact (hu.map f).ne_zero) (r ≫ h)
  obtain ⟨h', e₁, e₂⟩ := GlobalTheory.T.exists_torsion_lift_specialFibre_of_generic_rational GlobalTheory.T.point_descends_to_valuationRing' hL.unramExt u.V u.complete u.G (PadicAlgCl p) _ n hu
    (GlobalTheory.T.thetaModel_torsion_rational_over_fractionField o Ω S ρ p y₀ u n hd) κ f hf x hx
  obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.exists_label_of_pow_eq_one' o Ω S ρ p y₀ u n hd h' e₁
  refine ⟨b, hb, (H _ _ (GlobalTheory.T.modelPointExtendsTorsionPoint_mul o Ω S ρ p y₀ u a b h h' hh hb')).2 ?_⟩
  obtain rfl : r ≫ h' = x := Over.OverMorphism.ext e₂
  rw [← MonObj.comp_mul] at hx'
  rw [← IsLocalRing.comap_closedPoint f]
  exact hx'

theorem closure_unit_theta : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l hy
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n ^ (j + ρ.k * 2) := by rw [hr, ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + ρ.k * 2 := by have := ρ.two_le; omega
  have : NeZero (S.r * S.N) := ⟨by rw [hM]; exact pow_ne_zero _ ρ.n_prime.ne_zero⟩
  obtain ⟨c, hc, H⟩ := exists_bound hL hL₂ u hy ρ.n_prime.two_le (by rw [hM]; exact dvd_pow_self _ (by omega))
  have hle : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ := fun x =>
    le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove x
  obtain ⟨x₀, hx₀⟩ : ∃ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀ :=
    exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖)
  have hcδ : c ≤ S.delta y₀ := by
    obtain ⟨b, -, hb⟩ := (H 0 ((l.ker_iff 0).1 (zero_mem _))).2
    exact hb ▸ hle _
  have hδ := hc.trans_le hcδ
  have hsub : {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} ⊆ l.yy.ker := fun x hx => by
    have hx : ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀ := hx
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL₂ hT o Ω S ρ p y₀ u l hy x (norm_pos_iff.1 (hx ▸ hδ))
    rw [hx, le_mul_iff_one_le_right hδ, Real.one_le_exp_iff, neg_nonneg] at hw'
    have hpos : (0 : ℝ) < ((S.r * S.N : ℕ) : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (NeZero.pos _)) 2
    have hq : l.q w ≤ 0 := not_lt.1 fun h => (div_pos h hpos).not_ge hw'
    obtain rfl := eq_zero_of_nonpos l.q l.pos hq
    exact hw
  have hδc : S.delta y₀ = c := le_antisymm (hx₀ ▸ (H x₀ ((l.ker_iff x₀).1 (hsub hx₀))).1) hcδ
  refine ⟨hδ, GlobalTheory.T.closure_eq_ker_of_meets_torsion_cosets' _ _ ρ.n _ _ ρ.n_prime.ne_zero hJ hM l.yy l.yy_onto _ hsub fun a ha => ?_⟩
  obtain ⟨b, hb, hb'⟩ := (H a ((l.ker_iff a).1 ha)).2
  exact ⟨b, hb, hb'.trans hδc.symm⟩

end GlobalTheory.UnitTheta
end

