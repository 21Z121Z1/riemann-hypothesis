import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriods
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

namespace CoordProof

theorem diag_coords : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := GlobalTheory.T.lattice_deformation_multiplication

theorem exists_isDet : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := GlobalTheory.T.det_omega_eq_const_mul_det

theorem cmType_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := GlobalTheory.T.cm_type_separates_embeddings

theorem pull_ext {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e (by rw [Over.w x, Over.w y])

theorem jetRing_π_algebraMap {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (a : ℂ) : J.π (algebraMap ℂ J.B a) = a := by
  rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
  simp

theorem π_jet (hJ : JetCalc) {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) : J.π (jet J f) = f 0 := by
  obtain ⟨-, -, -, -, -, ht, -⟩ := hJ I n J
  simp only [jet, taylor, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [Algebra.smul_def, jetRing_π_algebraMap]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [Fin.prod_univ_succ, ht, zero_mul, mul_zero]
  · simp

end CoordProof

open CoordProof in

theorem coordEx (hGM : GlobalTheory.Published.GaussManinPeriods) (hJ : JetCalc) (hD : DiagFrame) : CoordEx := by
  obtain ⟨ε, GM⟩ := hGM
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G
  haveI := G.smooth
  have hX : ∀ z, ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (q : X'.A.left ⟶ G.X.A.left),
      X'.IsPullBy G.X (spMap (G.y z : G.B →+* ℂ)) q := fun z ↦ Obj.exists_isPullBy G.X _
  choose X q hq using hX
  have hδ : ∀ z, ∃ δ : (X z).DetGen, Obj.DetCorr (G.y z : G.B →+* ℂ) (q z) G.δ.1 δ.1 :=
    fun z ↦ ((hq z).existsUnique_detGen _ G.δ).exists
  choose δ hδ using hδ
  let mor : ∀ z, GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 ℂ) (𝟙 _) (X z).A (G.y z : G.B →+* ℂ)
      (spMap (G.y z : G.B →+* ℂ)) (q z) := fun z ↦
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hq z).grp
  have hπj : J.π.comp (G.j : G.B →+* J.B) = (G.y 0 : G.B →+* ℂ) := by
    ext b
    simp only [RingHom.comp_apply, RingHom.coe_coe, G.jet_eq, π_jet hJ]
  have h₀ : T.X.IsPullBy G.X (spMap (G.y 0 : G.B →+* ℂ)) (Y.i ≫ G.q) := by
    rw [← hπj, Cris.spMap_comp]
    exact Y.pull.comp G.pull
  obtain ⟨V, u, τ, P, P₀, hV, h0V, hVU, hper0, hper, -, hτ0, hτhol, hend, hPhol, hcrys⟩ :=
    GM G.B G.X.A _ G.X.ab G.X.dim I G.U G.y G.isOpen G.zero G.hol (fun z ↦ (X z).A) q (fun z ↦ (hq z).grp) mor
      (fun z ↦ (X z).diag T.U.c) (fun z ↦ LB.isLB_pull ((X z).isLB _) _) T.X.A (Y.i ≫ G.q) h₀.grp
      (T.X.diag T.U.c) (LB.isLB_pull (T.X.isLB _) _) T.U.u

  let ρ : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (T.U.e j) ((a : FR E) : E)
  have hreal : ∀ a j, starRingEnd ℂ (ρ a j) = ρ a j := fun a j ↦ (a : FR E).2 (φ (T.U.e j))
  have hsep : ∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k := fun j k hjk ↦
    cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hjk)
  let dg : 𝓞 (FR E) → (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun a ↦
    { toFun := fun w j ↦ ρ a j * w j
      map_add' := fun w w' ↦ funext fun j ↦ mul_add _ _ _
      map_smul' := fun s w ↦ funext fun j ↦ by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hdg : ∀ a w, dg a w = fun j ↦ ρ a j * w j := fun _ _ ↦ rfl
  have hact0 : ∀ a w, T.U.u.ex (dg a w) = T.U.u.ex w ≫ T.X.rm.act a := fun a w ↦ T.U.act a w
  have hΛ : ∀ a, ∀ x ∈ T.U.u.Λ, (fun j ↦ ρ a j * x j) ∈ T.U.u.Λ := fun a x hx ↦ by
    haveI := T.X.rm.hom a
    rw [← T.U.u.ker, ← hdg, hact0, (T.U.u.ker x).2 hx]
    exact H1.ClosedPointWeilPower.one_comp_hom _ inferInstance
  have hM0 : ∀ a w, (T.U.u.ex (dg a w)).left ≫ (Y.i ≫ G.q) =
      (T.U.u.ex w).left ≫ (Y.i ≫ G.q) ≫ (G.X.rm.act a).left := fun a w ↦ by
    rw [hact0, Over.comp_left, Category.assoc, h₀.act a]
  have hend' : ∀ z ∈ V, ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ w, ((u z).ex (M w)).left ≫ q z = ((u z).ex w).left ≫ q z ≫ (G.X.rm.act a).left) ∧
      ∀ x x' : T.U.u.Λ, (x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = dg a x → (τ z x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = M (τ z x) := fun z hz a ↦ by
    haveI := G.X.rm.hom a
    exact hend (G.X.rm.act a) (dg a) (hM0 a) z hz
  let τ' : (I → ℂ) → T.U.u.Λ →+ (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun z ↦ ((u z).Λ.subtype.toAddMonoidHom).comp (τ z).toAddMonoidHom
  have hτ' : ∀ z x, τ' z x = (τ z x : Fin (Module.finrank ℚ (FR E)) → ℂ) := fun _ _ ↦ rfl
  obtain ⟨V', D, ζ, hV', h0V', hV'V, hζ, hζ0, hζ1, hDτ, hDM⟩ := diag_coords (I → ℂ) _ (𝓞 (FR E)) ρ hreal hsep T.U.u.Λ
    T.U.u.discrete T.U.u.full hΛ V τ' hV h0V (fun x ↦ hτ0 x) (fun x ↦ hτhol x)
    (fun z hz a ↦ (hend' z hz a).imp fun M hM ↦ fun x x' hx ↦ hM.2 x x' hx)

  let ζ' : (I → ℂ) → I → ℂ := fun z i ↦ ζ z (T.U.e.symm i)
  have hdiff_ex : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L₁ L₂ : LB A.left} {g : ℕ} (u₁ : HolUnif A L₁ g) (u₂ : HolUnif A L₂ g),
      u₁.ex = u₂.ex → ∀ w v, u₂.IsDiff w v → u₁.IsDiff w v := by
    intro A _ L₁ L₂ g u₁ u₂ h w v hv
    simpa only [HolUnif.IsDiff, h] using hv
  have hU : ∀ z ∈ V', ∃ U : Unif φ (lattice c y) (ζ' z) (X z), U.e = T.U.e ∧ U.c = T.U.c ∧
      ∀ w v, (u z).IsDiff ((D z).symm w) v → U.u.IsDiff w v := by
    intro z hz
    have hzV := hV'V hz

    have hrm : ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
        (∀ w, (u z).ex (M w) = (u z).ex w ≫ (X z).rm.act a) ∧ ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
      intro a
      obtain ⟨M, hM1, hM2⟩ := hend' z hzV a
      refine ⟨M, fun w ↦ pull_ext (hq z).grp ?_, hDM z hz a M (fun x x' hx ↦ hM2 x x' hx)⟩
      rw [hM1, Over.comp_left, Category.assoc, (hq z).act a]
    obtain ⟨u1, hu1ex, hu1Λ, -, -, hu1d⟩ := GlobalTheory.exists_holUnif_reparam (X z).A _ _ (u z) (D z).symm (fun _ ↦ 1)
      (differentiable_const 1) (fun _ ↦ one_ne_zero) rfl
    have hact1 : ∀ (a : 𝓞 (FR E)) w, u1.ex (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = u1.ex w ≫ (X z).rm.act a := by
      intro a w
      obtain ⟨M, hM1, hM2⟩ := hrm a
      have : (D z).symm (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = M ((D z).symm w) := by
        apply (D z).injective
        rw [LinearEquiv.apply_symm_apply, hM2, LinearEquiv.apply_symm_apply]
      rw [hu1ex, hu1ex, this, hM1]
    obtain ⟨u2, hh, hex, χ, hAH⟩ := hD (FR E) 𝔠 (X z) T.U.c T.U.pos u1
      (fun j ↦ (φ (T.U.e j)).comp (algebraMap (FR E) E))
      (fun j k hjk ↦ by
        by_contra hne
        obtain ⟨a, ha⟩ := cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hne)
        exact ha (RingHom.congr_fun hjk (a : FR E)))
      hact1
    refine ⟨⟨T.U.e, T.U.c, T.U.pos, u2, fun w ↦ ?_, fun a w ↦ ?_, fun i ↦ hh (T.U.e.symm i), ?_⟩, rfl, rfl, ?_⟩
    · have hmem : w ∈ u2.Λ ↔ (D z).symm w ∈ (u z).Λ := by
        rw [← u2.ker w, hex, u1.ker w, hu1Λ w]
      rw [hmem]
      constructor
      · intro hw
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : T.U.u.Λ, (τ z x₀ : Fin (Module.finrank ℚ (FR E)) → ℂ) = (D z).symm w :=
          ⟨(τ z).symm ⟨_, hw⟩, by simp⟩
        obtain ⟨x, hxL, hx⟩ := (T.U.lat x₀).1 x₀.2
        refine ⟨x, hxL, ?_⟩
        have h1 := hDτ z hz x₀
        rw [hτ', hx₀, LinearEquiv.apply_symm_apply] at h1
        rw [h1]; funext j; simp [hx, defCoord, ζ']
      · rintro ⟨x, hxL, rfl⟩
        have hx₀ : (fun j ↦ defCoord φ 0 x (T.U.e j)) ∈ T.U.u.Λ := (T.U.lat _).2 ⟨x, hxL, rfl⟩
        have h1 := hDτ z hz ⟨_, hx₀⟩
        rw [hτ'] at h1
        have h2 : (fun j ↦ defCoord φ (ζ' z) x (T.U.e j)) = D z (τ z ⟨_, hx₀⟩) := by
          rw [h1]; funext j; simp [defCoord, ζ']
        rw [h2, LinearEquiv.symm_apply_apply]; exact (τ z _).2
    · rw [hex]; exact hact1 a w
    · simp only [Equiv.symm_apply_apply]; exact ⟨χ, hAH⟩
    · intro w v hv
      exact hdiff_ex u2 u1 hex w v (hu1d w v hv)

  choose U hUe hUc hUd using hU
  have hC : ∀ z (hz : z ∈ V'), ∃ C, (U z hz).IsDet (δ z).1 C := fun z hz ↦ exists_isDet (X z) _ (U z hz).u (δ z).1
  obtain ⟨-, -, -, -, -, hJt, hJprod⟩ := hJ I n J
  refine ⟨{
    V := V'
    isOpen := hV'
    zero := h0V'
    sub := hV'V.trans hVU
    X := X
    q := q
    pull := hq
    mor := mor
    δ := δ
    corr := hδ
    ζ := ζ'
    ζ_hol := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 hζ _
    ζ_zero := by funext i; simp [ζ', hζ0]
    ζ_mem := fun z hz i ↦ hζ1 z hz _
    U := U
    e_eq := hUe
    C := fun z ↦ if hz : z ∈ V' then Classical.choose (hC z hz) else 0
    det := fun z hz ↦ by simp only [dif_pos hz]; exact Classical.choose_spec (hC z hz)
    P₀ := P₀
    per := hper0
    P := fun z ↦ (P z).comp (τ z).toAddMonoidHom
    lie := fun z hz x ↦ by
      obtain ⟨v, hv1, hv2⟩ := (hper z (hV'V hz)).2.2.1 (τ z x)
      refine ⟨v, hv1, hUd z hz _ v ?_⟩
      have h1 : (fun a ↦ x.1 a + ζ' z (T.U.e a) * starRingEnd ℂ (x.1 a)) = D z (τ z x) := by
        rw [← hτ', hDτ z hz x]; funext a; simp [ζ']
      rw [h1, LinearEquiv.symm_apply_apply]; exact hv2
    P_hol := fun x c ↦ (hPhol x c).mono hV'V
    horiz := fun m' x d hd c ↦ hcrys J.B J.π J.κ J.nil (jetRing_π_algebraMap J) (n + 1) J.t hJt hJprod G.j G.jet_eq
      Y.X'.A G.q G.pull.grp m' Y.i Y.pull.grp rfl Y.mor x d hd c }⟩

end GlobalTheory.LatJet.An
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibEt

@[reassoc]
theorem map_fst' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.fst f' g' = pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.snd f' g' = pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem exists_residue_factor {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (s : S)
    (hs : π s = closedPoint R) :
    ∃ κ : ResidueField R →+* S.residueField s, S.fromSpecResidueField s ≫ π = spMap (κ.comp (residue R)) := by
  let φ := Spec.preimage (S.fromSpecResidueField s ≫ π)
  have hφ : Spec.map φ = S.fromSpecResidueField s ≫ π := Spec.map_preimage _
  have hpt : ∀ t : Spec (S.residueField s), (Spec.map φ) t = closedPoint R := by
    intro t
    rw [hφ, Scheme.Hom.comp_apply]
    have : S.fromSpecResidueField s t = s := by
      have := Set.mem_range_self (f := ⇑(S.fromSpecResidueField s)) t
      rwa [Scheme.range_fromSpecResidueField] at this
    rw [this, hs]
  have hker : ∀ r ∈ maximalIdeal R, φ.hom r = 0 := by
    intro r hr
    let t : Spec (S.residueField s) := closedPoint (S.residueField s)
    have h1 : (PrimeSpectrum.comap φ.hom t) = closedPoint R := hpt t
    have h2 : r ∈ (PrimeSpectrum.comap φ.hom t).asIdeal := by rw [h1]; exact hr
    simpa [t, closedPoint] using h2
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ.hom hker, ?_⟩
  rw [← hφ]
  rfl

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem smooth_affineSpace_sp (R : Type) [CommRing R] (g : ℕ) : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := by
  have e : (𝔸(Fin g; Sp R) ↘ Sp R) = (AffineSpace.isoOfIsAffine (Fin g) (Sp R)).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ (Sp R).isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := Fin g) (S := Sp R), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(Sp R, ⊤) (MvPolynomial (Fin g) Γ(Sp R, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(Sp R, ⊤)) (σ := Fin g)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

end GlobalTheory.Mum.FibEt

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.fibre_etale_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c hc1 hc2 z hz
  haveI : Smooth G'.hom := hG.smooth
  haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := FibEt.smooth_affineSpace_sp R g
  haveI : Etale e := he
  let iV : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ G'.left := (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι
  let p : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ M.S := iV ≫ G'.hom
  have hh : c ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) M.π = p := by
    rw [hc2]; simp only [p, iV, Category.assoc]
  have hp : Smooth p := by dsimp only [p, iV]; infer_instance
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by rw [reassoc_of% hab, E.f_over]
  have hs : M.π (p z) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι z)) key
    simp only [Scheme.Hom.comp_apply] at h1 hz ⊢
    simp only [p, iV, Scheme.Hom.comp_apply]
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨κ, hκ⟩ := FibEt.exists_residue_factor M.π (p z) hs
  obtain ⟨Ω', _, io, eG, l, -, hl1, hl2⟩ := E.fib (M.S.residueField (p z)) (M.S.fromSpecResidueField (p z)) κ hκ

  let Vs := (a ⁻¹ᵁ (b ⁻¹ᵁ W0))
  let x' : Sp Ω' ⟶ M.S := spMap io ≫ M.S.fromSpecResidueField (p z)
  let k' : Sp Ω' ⟶ Sp (ResidueField R) := spMap (io.comp κ)
  have hxk : x' ≫ M.π = k' ≫ spMap (residue R) := by
    simp only [x', k', Category.assoc, hκ, ← Spec.map_comp]; rfl
  have hpt : x' (closedPoint Ω') = p z := by
    simp only [x', Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := ⇑(M.S.fromSpecResidueField (p z))) ((spMap io) (closedPoint Ω'))
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x') z (closedPoint Ω') hpt.symm
  let mG : pullback p x' ⟶ pullback G'.hom x' :=
    pullback.map p x' G'.hom x' iV (𝟙 _) (𝟙 _) (by simp [p]) (by simp)
  let gm : pullback p x' ⟶ pullback E.Y.hom k' := mG ≫ eG.hom.left
  have hgms : gm ≫ pullback.snd E.Y.hom k' = pullback.snd p x' := by
    have hA : eG.hom.left ≫ pullback.snd E.Y.hom k' = pullback.snd G'.hom x' := Over.w eG.hom
    simp only [gm, Category.assoc, hA, mG, FibEt.map_snd', Category.comp_id]
  have E1 : mG ≫ l = pullback.fst p x' ≫ Vs.ι ≫ X.ι := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl1]
    exact FibEt.map_fst' _ _ _ _ _ _ _ _ _
  have E2 : gm ≫ pullback.fst E.Y.hom k' ≫ E.j = pullback.fst p x' ≫ Vs.ι ≫ a ≫ b := by
    simp only [gm, Category.assoc]
    erw [← hl2]
    rw [reassoc_of% E1, hab]
  have hgmw : (gm ≫ pullback.fst E.Y.hom k') w = y := by
    haveI : IsImmersion E.j := E.imm
    apply E.j.isEmbedding.injective
    have h := congrArg (fun f : pullback p x' ⟶ PSpace R E.N => f w) E2
    simp only [Scheme.Hom.comp_apply] at h hz ⊢
    rw [h, hw1, hz, hyb]
  let Wo : (pullback p x').Opens := (gm ≫ pullback.fst E.Y.hom k') ⁻¹ᵁ O
  have hwW : w ∈ Wo := by
    show (gm ≫ pullback.fst E.Y.hom k') w ∈ O
    rw [hgmw]; exact hyO

  let A := 𝔸(Fin g; Sp R) ↘ Sp R
  let Oy := pullback (O.ι ≫ E.Y.hom) k'
  let eΩ : Oy ⟶ pullback (pullback.snd A (spMap (residue R))) k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' (pullback.snd A (spMap (residue R))) k' e (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, he2]) (by simp)
  haveI : MorphismProperty.IsStableUnderComposition @Etale := MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have heΩ : Etale eΩ :=
    MorphismProperty.pullback_map (P := @Etale) (f := O.ι ≫ E.Y.hom) (g := k') (f' := pullback.snd A (spMap (residue R)))
      (g' := k') (i₁ := e) (i₂ := 𝟙 _) he inferInstance he2.symm (by simp)
  let θ : pullback (pullback.snd A (spMap (residue R))) k' ⟶ pullback (pullback.snd A M.π) x' :=
    (pullbackLeftPullbackSndIso A (spMap (residue R)) k').hom ≫ (pullback.congrHom rfl hxk.symm).hom ≫
      (pullbackLeftPullbackSndIso A M.π x').inv
  have hθ1 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.fst A M.π =
      pullback.fst (pullback.snd A (spMap (residue R))) k' ≫ pullback.fst A (spMap (residue R)) := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, FibEt.map_fst',
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hθ2 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.snd A M.π =
      pullback.snd (pullback.snd A (spMap (residue R))) k' ≫ x' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_hom, FibEt.map_snd'_assoc,
      Category.id_comp]
    simp
  have hθ3 : θ ≫ pullback.snd (pullback.snd A M.π) x' = pullback.snd (pullback.snd A (spMap (residue R))) k' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, FibEt.map_snd',
      Category.comp_id]
    simp

  let ψ : Wo.toScheme ⟶ Oy :=
    pullback.lift ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) (Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k') (by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, pullback.condition]
      rfl)
  have hψ1 : ψ ≫ pullback.fst (O.ι ≫ E.Y.hom) k' = (gm ≫ pullback.fst E.Y.hom k') ∣_ O := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd (O.ι ≫ E.Y.hom) k' = Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k' := pullback.lift_snd _ _ _
  let jO : Oy ⟶ pullback E.Y.hom k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' E.Y.hom k' O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsOpenImmersion jO :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := O.ι ≫ E.Y.hom) (g := k') (f' := E.Y.hom) (g' := k')
      (i₁ := O.ι) (i₂ := 𝟙 _) inferInstance inferInstance rfl (by simp)
  haveI : IsOpenImmersion mG :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := p) (g := x') (f' := G'.hom) (g' := x')
      (i₁ := iV) (i₂ := 𝟙 _) (by dsimp only [iV]; infer_instance) inferInstance rfl (by simp)
  haveI : IsIso eG.hom.left := by
    show IsIso ((Over.forget _).map eG.hom); infer_instance
  have hψj : ψ ≫ jO = Wo.ι ≫ gm := by
    apply pullback.hom_ext
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_fst', reassoc_of% hψ1, morphismRestrict_ι]
      simp only [Category.assoc]
      rfl
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_snd', Category.comp_id, hψ2]
      simp only [Category.assoc]
  haveI : IsOpenImmersion (ψ ≫ jO) := by rw [hψj]; dsimp only [gm]; infer_instance
  haveI : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ jO
  have hEq : Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp) = ψ ≫ eΩ ≫ θ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · have hcond : (Wo.ι ≫ pullback.fst p x' ≫ (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0)) ≫ W0.ι =
            ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) ≫ O.ι ≫ E.j := by
          simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
          rw [E2]
        simp only [Category.assoc]
        rw [hθ1, FibEt.map_fst'_assoc, hc1]
        dsimp only [eΩ]
        rw [FibEt.map_fst'_assoc, reassoc_of% hψ1, he3 _ _ _ hcond]
        simp only [Category.assoc]
      · simp only [Category.assoc]
        rw [hθ2, FibEt.map_fst'_assoc, hh]
        dsimp only [eΩ]
        rw [FibEt.map_snd'_assoc, Category.id_comp, reassoc_of% hψ2]
        rw [reassoc_of% hgms, pullback.condition]
    · simp only [Category.assoc]
      rw [hθ3, FibEt.map_snd', Category.comp_id]
      dsimp only [eΩ]
      rw [FibEt.map_snd', Category.comp_id, hψ2, hgms]
  have hEt : Etale (Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp)) := by
    rw [hEq]; infer_instance
  obtain ⟨U, hU, hUe⟩ := GlobalTheory.Mum.etale_near_of_etale_fibre M.S Vs.toScheme _ p (pullback.snd A M.π) c hh hp inferInstance Ω' x' Wo w hwW hEt
  exact ⟨U, hw1 ▸ hU, hUe⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianScheme
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_mul_all (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A) :
    tanVal (a * b) f = tanVal a f + tanVal b f := by
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison hC hH) R A g hA hg).1
  have hc : Form.cl _ f ∈ prim (dp0 R) (𝟙 _) A := by rw [hP]; trivial
  rw [mem_prim_iff] at hc
  have mμ : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R) (μ[A]).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m1 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.fst A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m2 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.snd A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have e0 : pullOver (dp0 R) (𝟙 _) μ[A] (Form.cl _ f) = mμ.pull1 (Form.cl _ f) := rfl
  have e1 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.fst A A) (Form.cl _ f) =
    m1.pull1 (Form.cl _ f) := rfl
  have e2 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.snd A A) (Form.cl _ f) =
    m2.pull1 (Form.cl _ f) := rfl
  have hcl : Form.cl _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    ((map_sub _ _ _).trans (congrArg₂ (· - ·) (IsMor.cl_pullForm mμ f)
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (IsMor.cl_pullForm m1 f) (IsMor.cl_pullForm m2 f))))).trans
      ((congrArg₂ (· - ·) e0 (congrArg₂ (· + ·) e1 e2)).symm.trans (sub_eq_zero.2 hc))
  have hinj : Function.Injective (GlobalTheory.CechDR.clForm ((A ⊗ A).hom ≫ 𝟙 (Sp R))) :=
    (hH R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hg2).2.2.2.2.1.2.1
  have hcmp : GlobalTheory.CechDR.cmpForm _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    hinj (((GlobalTheory.CechDR.comparison_formClass _ _).symm.trans ((congrArg _ hcl).trans (map_zero _))).trans (map_zero _).symm)
  have h0 := GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R (A ⊗ A) (lift a b) _ hcmp
  have h1 : tanVal (lift a b) (mμ.pullForm f) = tanVal (lift a b) (m1.pullForm f + m2.pullForm f) :=
    sub_eq_zero.1 ((map_sub _ _ _).symm.trans h0)
  calc tanVal (a * b) f = tanVal (lift a b ≫ μ[A]) f := by rw [Hom.mul_def]
    _ = tanVal (lift a b) (mμ.pullForm f) := tanVal_comp _ _ mμ f
    _ = tanVal (lift a b) (m1.pullForm f) + tanVal (lift a b) (m2.pullForm f) := h1.trans (map_add _ _ _)
    _ = tanVal (lift a b ≫ SemiCartesianMonoidalCategory.fst A A) f +
        tanVal (lift a b ≫ SemiCartesianMonoidalCategory.snd A A) f :=
      (congrArg₂ (· + ·) (tanVal_comp _ _ m1 f) (tanVal_comp _ _ m2 f)).symm
    _ = tanVal a f + tanVal b f :=
      congrArg₂ (fun x y ↦ tanVal x f + tanVal y f) (lift_fst a b) (lift_snd a b)

end GlobalTheory.TanAdd
end
end

