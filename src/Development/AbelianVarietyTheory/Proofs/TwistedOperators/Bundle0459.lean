import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctionalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  first | exact @GlobalTheory.PerAllTame.perAll_tame | exact GlobalTheory.PerAllTame.perAll_tame | (intros; apply GlobalTheory.PerAllTame.perAll_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_proj {K M : Type} [Field K] [AddCommGroup M] [Module K M] (U : Submodule K M) :
    ∃ Q : M →ₗ[K] M, (∀ x ∈ U, Q x = 0) ∧ ∀ x, x - Q x ∈ U := by
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨LinearMap.id - U.subtype ∘ₗ U.projectionOnto W hW, fun x hx => ?_, fun x => ?_⟩
  · have := Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩
    simp [this]
  · simp

theorem exists_lattice {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (Λ : Submodule O (Fin n → K))
    (h : Λ.FG) : ∃ (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (Λ' : Submodule O (Fin n → K)),
      Submodule.IsLattice K Λ' ∧ Λ ≤ Λ' ∧ (∀ x ∈ Λ, Q x = 0) ∧ ∀ x ∈ Λ', Q x = 0 → x ∈ Λ := by
  obtain ⟨Q, h1, h2⟩ := exists_proj (Submodule.span K (Λ : Set (Fin n → K)))
  have h3 : ∀ x, Q (Q x) = Q x := fun x => by
    have := h1 _ (h2 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨Q, Λ ⊔ Submodule.span O (Set.range fun j : Fin n => Q (Pi.single j 1)), ⟨?_, ?_⟩, le_sup_left,
    fun x hx => h1 x (Submodule.subset_span hx), fun x hx h0 => ?_⟩
  · exact h.sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, ← sub_add_cancel (Pi.single j 1 : Fin n → K) (Q (Pi.single j 1))]
    refine add_mem (Submodule.span_mono ?_ (h2 _)) (Submodule.subset_span ?_)
    · exact fun y hy => Submodule.mem_sup_left hy
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h4 : Q b = b := by
      refine Submodule.span_induction (p := fun b _ => Q b = b) ?_ (map_zero Q) ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        exact h3 _
      · intro x y _ _ hx hy
        rw [map_add, hx, hy]
      · intro c x _ hx
        rw [← algebraMap_smul K c x, map_smul, hx]
    rw [map_add, h1 a (Submodule.subset_span ha), h4, zero_add] at h0
    rwa [h0, add_zero]

theorem map_mulVec_gen {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) {n : ℕ}
    (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (LinearMap.toMatrix' Q).map f *ᵥ (fun i => f (x i)) = fun i => f (Q x i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec, RingHom.map_mulVec]
  rfl

variable {D : D7}

theorem inc_injective : Function.Injective (inc D) := by
  obtain ⟨P, hP, h0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField D.host.E) |>.imp fun _ h => h.symm
  intro a b hab
  have := congrArg (GlobalTheory.StdFrames.cpt (D := D) ⟨P, hP.isPrime, h0⟩) hab
  rw [cpt_inc, cpt_inc] at this
  exact (algebraMap D.host.E _).injective this

theorem mem_of_inc_mem_hat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    {x : Fin n → D.host.E} (hx : (fun i => inc D (x i)) ∈ hat Λ) : x ∈ Λ := by
  obtain ⟨Q, Λ', h1, h2, h3, h4⟩ := exists_lattice Λ h
  refine h4 x ((inc_mem_hat_iff h1 x).1 (hat_mono h2 hx)) ?_
  have h5 : (LinearMap.toMatrix' Q).map (inc D) *ᵥ (fun i => inc D (x i)) = 0 := by
    refine hat_induction (p := fun y => (LinearMap.toMatrix' Q).map (inc D) *ᵥ y = 0) ?_ (mulVec_zero _) ?_ ?_ hx
    · intro y hy
      rw [map_mulVec_gen, h3 y hy]
      funext i
      exact RingHom.map_zero _
    · intro a b ha hb
      rw [mulVec_add, ha, hb, add_zero]
    · intro a _ b hb
      rw [mulVec_smul, hb, smul_zero]
  rw [map_mulVec_gen] at h5
  funext i
  exact inc_injective ((congrFun h5 i).trans (RingHom.map_zero _).symm)

theorem inCmp_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y L) y ↔ InCmp (idem w) (Formalism.L2.Herm.crdLat Y L') y := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · rcases (T_mem_iff hπ w).1 hT with hw | hw
    · exact ((h.2.2 w _ (isPlIdem_idem w) hw).1 y).trans ((h'.2.2 w _ (isPlIdem_idem w) hw).1 y).symm
    · have a := h.2.2 _ _ (isPlIdem_idem _) hw
      have a' := h'.2.2 _ _ (isPlIdem_idem _) hw
      rw [cjA_idem, GlobalTheory.StdFrames.cP_cP] at a a'
      refine (a.2 y).trans (Iff.trans ?_ (a'.2 y).symm)
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y' => ?_
      rw [a.1 y', a'.1 y']
  · exact (h.2.1 w _ (isPlIdem_idem w) hT y).trans (h'.2.1 w _ (isPlIdem_idem w) hT y).symm

theorem glued_le {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') : L ≤ L' := by
  intro x hx
  have hfg : (Formalism.L2.Herm.crdLat Y L').FG := h'.1.map _
  have h1 : vA Y x ∈ hat (Formalism.L2.Herm.crdLat Y L') := mem_hat_of_idem hfg fun w =>
    ((inCmp_iff hπ h h' w _).1 ⟨smul_mem_hat (idem_mem w) (vA_mem_hat Y hx), by rw [smul_smul, idem_mul_self]⟩).1
  obtain ⟨x', hx', e⟩ := mem_of_inc_mem_hat hfg h1
  rwa [← (Formalism.L2.Herm.crd Y).injective e]

theorem glued_unique (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (Y X : HSp D)
    (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L L' : Submodule (𝓞 D.host.E) Y.V) (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') :
    L = L' :=
  le_antisymm (glued_le hπ h h') (glued_le hπ h' h)

end GlobalTheory.GlueUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMuStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  first | exact @GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | exact GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | (intros; apply GlobalTheory.HeckeEx.frame_pull_eq_transition_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKerLatticeBounds
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeKerIdx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ex_smul_act (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (c : ℂ) (r : 𝓞 E) (v : (F.Di i).La) :
    F.ex i P (c • P (r • v)) = F.ex i P (c • P v) ≫ Xo.univ.t.act.act r := by
  rw [← F.ex_lin i P hP]
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, hP.1]
  ring

theorem inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ))⁻¹ • P ((n : 𝓞 E) • w) = P w := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

theorem sq_inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ) ^ 2)⁻¹ • P ((n : 𝓞 E) • w) = (n : ℂ)⁻¹ • P w := by
  rw [pow_two, mul_inv, mul_smul, inv_smul_natCast P hn]

theorem mem_span_smul_top {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (n : ℕ) (x : La) :
    x ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) La) ↔ ∃ b, (n : 𝓞 E) • b = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

end GlobalTheory.HeckeKerIdx

open GlobalTheory.HeckeKerIdx in

theorem GlobalTheory.heckeKer_lattice_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (𝔓 : Ideal (𝓞 E)) (p k : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (M : Submodule (𝓞 E) (F.Di i).La), IsPeriod (F.Di i) ty P → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p → Xo.univ.t.HeckeKer (Over.mk (F.u i P)) Dw 𝔓 p k C → (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ a ∈ M) → (Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ M ∧ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • M ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧ Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸ M.comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) = Ideal.absNorm 𝔓 ^ k := by
  intro E _ _ _ H Dw l Xo σ g ty F i P 𝔓 p k C M hP hH hK hM
  obtain ⟨-, -, -, hp, hp𝔓⟩ := hH
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro x hx a _
    obtain ⟨π, hπ, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    obtain ⟨J, hJ⟩ : 𝔓 ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hp𝔓)
    rw [← hM, mul_smul, sq_inv_smul_natCast P hp0]
    refine hK.2.1 J (by rw [hJ, mul_comm]) fun j hj => ?_
    rw [← ex_smul_act F i P hP, smul_smul]
    have hjπ : j * π ∈ Ideal.span {(p : 𝓞 E)} := by
      rw [hJ, mul_comm j]
      exact Ideal.mul_mem_mul hπ hj
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hjπ
    rw [hc, mul_smul, inv_smul_natCast P hp0]
    exact (F.ex_ker i P hP _).2 ⟨_, rfl⟩
  · rw [Submodule.smul_le]
    intro r hr a ha
    have h1 := hK.2.2.1 ((hM a).2 ha) ((p : 𝓞 E) * r)
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    rw [← ex_smul_act F i P hP, mul_smul, sq_inv_smul_natCast P hp0, F.ex_ker i P hP] at h1
    obtain ⟨b, hb⟩ := h1
    rw [mem_span_smul_top]
    refine ⟨b, hP.2.1 ?_⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  · set N : Submodule (𝓞 E) (F.Di i).La := Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) with hN
    set Tp := GlobalTheory.HeckeKerModel.torsSub Xo.univ.t (Over.mk (F.u i P)) p with hTp
    have hmemTp : ∀ y, y ∈ Tp ↔ y ^ p = 1 := fun y => GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t y p
    have hpow : ∀ w, F.ex i P w ^ p = F.ex i P (p • w) := fun w => (GlobalTheory.HeckeKerLat.ex_nsmul F i P hP p w).symm
    have hinvmem : ∀ b, F.ex i P ((p : ℂ)⁻¹ • P b) ∈ Tp := fun b => by
      rw [hmemTp, hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
      exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
    have hmemN : ∀ x ∈ N, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x) ∈ Tp := fun x hx => by
      obtain ⟨b, rfl⟩ := (mem_span_smul_top p x).1 hx
      rw [sq_inv_smul_natCast P hp0]
      exact hinvmem b
    let fA : ↥N →+ Additive ↥Tp :=
      { toFun := fun x => Additive.ofMul ⟨F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x), hmemN x.1 x.2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P 0) = 1
          rw [map_zero, smul_zero]
          exact (F.ex_ker i P hP 0).2 (zero_mem _)
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P (x.1 + y.1)) = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x.1) * F.ex i P (((p : ℂ) ^ 2)⁻¹ • P y.1)
          rw [map_add, smul_add, F.ex_add i P hP] }
    let h0 : (F.Di i).La →+ ↥N :=
      { toFun := fun a => ⟨(p : 𝓞 E) • a, (mem_span_smul_top p _).2 ⟨a, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp [smul_add] }
    have hgsurj : Function.Surjective (fA.comp h0) := by
      intro y
      obtain ⟨w, hw⟩ := F.ex_onto i P hP (Additive.toMul y).1
      have h1 : F.ex i P (p • w) = 1 := by rw [← hpow, hw]; exact (hmemTp _).1 (Additive.toMul y).2
      obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 h1
      refine ⟨a, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • a)) = (Additive.toMul y).1
      rw [sq_inv_smul_natCast P hp0, ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hpC, one_smul, hw]
    have hsurj : Function.Surjective fA := fun y => by
      obtain ⟨a, ha⟩ := hgsurj y
      exact ⟨h0 a, ha⟩
    set H' : AddSubgroup (Additive ↥Tp) := Subgroup.toAddSubgroup (C.subgroupOf Tp) with hH'
    have hker : (M.comap N.subtype).toAddSubgroup = H'.comap fA := by
      ext x
      rw [AddSubgroup.mem_comap]
      show x.1 ∈ M ↔ _
      rw [← hM]
      rfl
    have hidx : Nat.card (↥N ⧸ M.comap N.subtype) = H'.index := by
      rw [← AddSubgroup.index_comap_of_surjective H' hsurj, ← hker]
      rfl
    have hcardTp : Nat.card (Additive ↥Tp) = Nat.card (Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)})) := rfl
    have hcardH : Nat.card H' = Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) :=
      Nat.card_congr
        { toFun := fun z => ⟨(Additive.toMul z.1).1, z.2, (Additive.toMul z.1).2⟩
          invFun := fun z => ⟨Additive.ofMul ⟨z.1, z.2.2⟩, z.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hfin : Nat.card (Additive ↥Tp) ≠ 0 := by
      have := (F.Di i).fin
      have := GlobalTheory.datum_free_int (F.Di i)
      have : Module.Finite ℤ (F.Di i).La := Module.Finite.trans (𝓞 E) (F.Di i).La
      have hle : (nsmulAddMonoidHom (α := (F.Di i).La) p).range ≤ (fA.comp h0).ker := by
        rintro _ ⟨b, rfl⟩
        rw [AddMonoidHom.mem_ker]
        apply Additive.toMul.injective
        apply Subtype.ext
        show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • (p • b))) = 1
        rw [sq_inv_smul_natCast P hp0, ← Nat.cast_smul_eq_nsmul (𝓞 E), inv_smul_natCast P hp0]
        exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
      have hd := AddSubgroup.index_dvd_of_le hle
      rw [AddSubgroup.index_range_nsmul, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hgsurj,
        AddSubgroup.card_top] at hd
      intro h0'
      rw [h0', zero_dvd_iff] at hd
      exact pow_ne_zero _ hp0 hd
    have key := H'.index_mul_card
    rw [hcardTp, hK.2.2.2.2.2, hcardH] at key
    rw [hidx]
    have hc : Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ≠ 0 := by
      intro hc0
      apply hfin
      rw [hcardTp, hK.2.2.2.2.2, hc0, zero_mul]
    rw [mul_comm (Nat.card _) (Ideal.absNorm 𝔓 ^ k)] at key
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeWeight
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeckePointLaw (scaleAt tanMap tanMap_scale scaleAt_comm isCombAt_iff tanMap_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comp_listProd {X Y : Over Xo.X} (f : X ⟶ Y) (L : List (Y ⟶ Xo.univ.t.G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons b L ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (h : IsLinHom ψ) (p : ℕ)
    {m : ℕ} {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ k, IsLieImg p ψ (v k) (v' k))
    {cf : Fin m → Ω} {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (hw : IsCombAt x v cf w)
    (hw' : IsCombAt x' v' cf w') (ht : IsTanAt x w) (ht' : IsTanAt x' w') : IsLieImg p ψ w w' := by
  choose a ha hpa using fun k => (hv k).2.2
  let b : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun k => Over.homMk (v' k) (hv k).2.1.1
  have hb : ∀ k, tanMap h (a k) = scaleAt x' p ≫ b k := fun k => Over.OverMorphism.ext (by
    rw [tanMap_left, Over.comp_left, ← hpa k]; rfl)
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w ht.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' ht'.1
  have eW : (List.ofFn fun k => scaleAt x (cf k) ≫ a k).prod = W := by
    rw [← isCombAt_iff]
    have : v = fun k => (a k).left := funext fun k => (ha k).symm
    subst this
    exact hw
  have eW' : (List.ofFn fun k => scaleAt x' (cf k) ≫ b k).prod = W' := (isCombAt_iff b cf W').1 hw'
  refine ⟨ht, ht', W, rfl, ?_⟩
  have key : scaleAt x' p ≫ W' = tanMap h W := by
    rw [← eW, ← eW', comp_listProd, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [tanMap_scale, hb, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  have := congrArg (·.left) key
  simp only [Over.comp_left, tanMap_left] at this
  exact this

open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt) in

theorem hkVal_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  intro E _ _ _ H Dw l Xo c P p i a n hA hT hF f hf Ω _ _ _ t y y' hB
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsSplitOff l P p := hA
  obtain ⟨g, hgt, hgd, hch⟩ := (frBor_iff_frChg y y' t).1 hB
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hgt τ i j hij)]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => by rw [hgd]; exact Units.ne_zero _)
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  obtain rfl : x' = y.x := hch.1
  have hw0 : wchar (ex Dw a n) t ≠ (0 : Ω) := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (t j).ne_zero
  have key : ∀ C : hkKer (Xo := Xo) P p i Ω y,
      hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C =
      wchar (ex Dw a n) t * hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f y C := by
    intro C
    have ex' := hT Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
    have ex := hT Ω y C
    unfold hkTerm
    rw [dif_pos ex', dif_pos ex]
    have hz' := ex'.choose_spec
    have hz := ex.choose_spec
    generalize ex'.choose = z' at hz' ⊢
    generalize ex.choose = z at hz ⊢
    obtain ⟨ψ, hψ, hL, hθ⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hS _ y C.1 z).1 hz
    rw [hkTr, Equiv.apply_symm_apply] at hθ
    obtain ⟨z'', hz'', -⟩ := existsUnique_frChg E H Dw l Xo c Ω z g (t none) hdet
    have hB' : FrBor t z z'' := (frBor_iff_frChg _ _ t).2 ⟨g, hgt, hgd, hz''⟩
    obtain ⟨x'', xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := z''
    obtain rfl : x'' = z.x := hz''.1
    have hP : hkRelFr P p i (hkTr Xo c p) Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := by
      show HkPt p (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩
      refine (GlobalTheory.HeckeFrCompare.hkPt_iff hS (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩).2 ⟨ψ, hψ, fun τ j => ?_, ?_⟩
      · exact GlobalTheory.HeckeWeight.isLieImg_comb hψ.2.1 p (hL τ) (hch.2.1 τ j) (hz''.2.1 τ j) (tan' τ j) (tan'' τ j)
      · rw [hkTr, Equiv.apply_symm_apply]
        exact hθ.smul (toΓ Ω (t none : Ω)) ((ChgOf.secBC_id_iff _ _ _ _).1 hch.2.2)
          ((ChgOf.secBC_id_iff _ _ _ _).1 hz''.2.2)
    obtain rfl := (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').1 _ _
      (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').2.1 (hF Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C z' _ hz' hP)
    exact (algebraic_laws lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance a n f hf t z _ hB'
  unfold hkVal
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.HeckeWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPointsStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeThetaTrace_values_at_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  first | exact @GlobalTheory.HeckeValues.hkPtC_values | exact GlobalTheory.HeckeValues.hkPtC_values | (intros; apply GlobalTheory.HeckeValues.hkPtC_values <;> assumption)
end

