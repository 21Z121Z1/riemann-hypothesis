import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Filter GlobalTheory.HolHom

namespace GlobalTheory.ShFam.HorLift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_of_comp_open {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [valAt'_eq_valR, valR_comp] at this
    exact this
  exact key U (i.preimage_image_eq U) f

theorem differentiableAt_dir [FiniteDimensional ℂ V] {G' G₀ G₁ S' S₀ S₁ : Scheme.{0}} {φ₀ : G' ⟶ G₀} {φ₁ : G' ⟶ G₁}
    {p : G' ⟶ S'} {p₀ : G₀ ⟶ S₀} {p₁ : G₁ ⟶ S₁} {f₀ : S' ⟶ S₀} {f₁ : S' ⟶ S₁} (H₀ : IsPullback φ₀ p p₀ f₀)
    (H₁ : IsPullback φ₁ p p₁ f₁) {g : ℕ} {B : Set V} {y : V → (Sp ℂ ⟶ S')} (hy : IsHolTo B y)
    {ex : V → (Fin g → ℂ) → (Sp ℂ ⟶ G₀)}
    (hex : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => ex bz.1 bz.2)
    (hover : ∀ b ∈ B, ∀ w, ex b w ≫ p₀ = y b ≫ f₀) {b₀ : V} (hb₀ : b₀ ∈ B)
    (hinj : ∀ w, IsDerivAt (ex b₀) 0 w (constVec (ex b₀ 0)) → w = 0) {v : V → (Sp (DualNumber ℂ) ⟶ G₁)}
    (hv : HolTan B v) {W : V → Fin g → ℂ}
    (hW : ∀ b ∈ B, ∃ v₀ : Sp (DualNumber ℂ) ⟶ G', v₀ ≫ p = constVec (y b) ∧ v₀ ≫ φ₁ = v b ∧
      IsDerivAt0 (ex b) (W b) (v₀ ≫ φ₀)) : DifferentiableAt ℂ W b₀ := by
  haveI : Nonempty (Sp ℂ ⟶ G') := ⟨H₀.lift _ _ (hover b₀ hb₀ 0)⟩
  choose! e h₀ hp using fun b (hb : b ∈ B) w =>
    (⟨H₀.lift _ _ (hover b hb w), H₀.lift_fst _ _ _, H₀.lift_snd _ _ _⟩ :
      ∃ x : Sp ℂ ⟶ G', x ≫ φ₀ = ex b w ∧ x ≫ p = y b)
  have hO := isOpen_of_isHolTo hex
  have he : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 := by
    have h1 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ φ₀) hex
      fun bz hb => h₀ _ hb.1 _
    have h2 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ p)
      (LocLift.isHolTo_comp hy hO differentiableOn_fst fun _ hb => hb.1) fun bz hb => hp _ hb.1 _
    exact isHolTo_of_holAt hO fun z hz =>
      holAt_of_isPullback H₀ (holAt_of_isHolTo h1 hz) (holAt_of_isHolTo h2 hz)
  have hsl : ∀ b ∈ B, HolAt (e b) 0 := fun b hb =>
    (holAt_of_isHolTo he (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  have hder : ∀ b ∈ B, ∀ w, ∃ u, IsDerivAt (e b) 0 w u ∧ IsDerivAt (ex b) 0 w (u ≫ φ₀) ∧
      u ≫ p = constVec (y b) := fun b hb w => by
    obtain ⟨u, hu⟩ := (hsl b hb).exists_isDerivAt w
    have h1 := hu.comp φ₀
    have h2 := hu.comp p
    simp only [h₀ b hb, hp b hb] at h1 h2
    exact ⟨u, hu, h1, h2.unique (isDerivAt_const _ _ _)⟩
  have hv' : ∀ b ∈ B, IsDerivAt (fun w => e b w ≫ φ₁) 0 (W b) (v b) := fun b hb => by
    obtain ⟨v₀, a1, a2, a3⟩ := hW b hb
    obtain ⟨u, hu, h1, h2⟩ := hder b hb (W b)
    obtain rfl : u = v₀ := H₀.hom_ext (h1.unique ((isDerivAt0_iff _ _ _).1 a3)) (h2.trans a1.symm)
    exact a2 ▸ hu.comp φ₁
  have he₁ := LocLift.isHolTo_comp_hom he φ₁
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => hinj w ?_
  obtain ⟨u, hu, h1, h2⟩ := hder b₀ hb₀ w
  have h3 : IsDerivAt (fun w => e b₀ w ≫ φ₁) 0 w (constVec (e b₀ 0 ≫ φ₁)) := by
    refine (isDerivAt_constVec_iff (c := fun w => e b₀ w ≫ φ₁)).2 fun U hU f => ?_
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z ≫ φ₁) U f) 0)
      (differentiableAt_partial (he₁ U f).1 (he₁ U f).2 ⟨⟨hb₀, trivial⟩, hU⟩) ?_
    have hc : ContinuousAt (fun b : V => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
    have hn := hc.eventually ((he₁ U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)
    refine ((hv U f).differentiableAt (hn.mono fun b hb =>
      ⟨hb.1.1, (le_preimage_dual_iff (hv' b hb.1.1).1 U).2 hb.2⟩)).congr_of_eventuallyEq ?_
    exact hn.mono fun b hb => ((hv' b hb.1.1).2 U hb.2 f).symm
  obtain rfl : u = constVec (e b₀ 0) := H₁.hom_ext ((hu.comp φ₁).unique h3)
    (by rw [h2, Category.assoc, hp b₀ hb₀])
  rwa [Category.assoc, h₀ b₀ hb₀] at h1

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw}

theorem exists_inner_lift (x : CxPts (genStr Z) σ) (hx : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact not_not.1 hx

theorem exists_dirs (Fu : Fam Xo c σ e) (a : CxFr Z σ) (y : Sp ℂ ⟶ Xo.XF c) (hy : y ≫ Z.jQ = a.1.1) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : Fu.u i P = y ≫ pullback.fst _ _) :
    ∃ (w : Fin g → Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ), (∀ j, M *ᵥ w j = Pi.single j 1) ∧
      ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
        v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
        IsDerivAt0 (fun w => (Fu.ex i P w).left) (w (e.symm z)) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]; exact a.1.2
  obtain ⟨y', v, hx, hv⟩ := @OpenReg.exists_frPt_of_eigFrame E _ _ _ H Dw l Xo c O _ β Z (CAt σ) inferInstance
    (inferInstanceAs (IsLocalRing ℂ)) inferInstance y hs (a.1.1 ≫ genι Z)
    (by rw [← hy]; exact (Category.assoc _ _ _).symm) a.2
  obtain ⟨w, M, -, hw, hM, -⟩ := AdaptedPeriods.exists_adapted E H Dw l Xo c σ g e Fu y' i P hP (hu.trans hx.symm)
  refine ⟨w, M, hM, fun z => ⟨v z.1 z.2, (hv _ _).1, (hv _ _).2.2, ?_⟩⟩
  have := hw (e.symm z)
  rw [Equiv.apply_symm_apply, ← (hv _ _).2.1] at this
  exact this

theorem exists_hol_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu V _ _ _ B a hB ha hI b₀ hb₀
  haveI := Z.jQ_open
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(exists_inner_lift _ (hI b₀ hb₀)).choose⟩
  choose! y hy using fun b (hb : b ∈ B) => exists_inner_lift _ (hI b hb)
  have hyh : IsHolTo B y := isHolTo_of_comp_open Z.jQ (LocLift.isHolTo_congr ha.1 hy)
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hBφ : IsOpen (φ.symm ⁻¹' B) := hB.preimage φ.symm.continuous
  obtain ⟨B₁, i, P₁, hB₁, hb₁, hsub, hP₁, hu₁⟩ := Fu.lift _ (φ.symm ⁻¹' B) (fun t => y (φ.symm t) ≫ pullback.fst _ _) hBφ
    (fun t ht => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← Z.jQ_over, ← Category.assoc, hy _ ht,
        ← OpenReg.spMap_comp]
      exact congrArg (· ≫ _) (a _).1.2)
    (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom hyh _) hBφ φ.symm.differentiableOn fun _ h => h) (φ b₀)
    (by simpa using hb₀)
  have hB' : IsOpen (φ ⁻¹' B₁) := hB₁.preimage φ.continuous
  have hsub' : φ ⁻¹' B₁ ⊆ B := fun b hb => by simpa using hsub hb
  have hu : ∀ b ∈ φ ⁻¹' B₁, Fu.u i (P₁ (φ b)) = y b ≫ pullback.fst _ _ := fun b hb => by simpa using hu₁ _ hb
  have hex : IsHolTo ((φ ⁻¹' B₁) ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => (Fu.ex i (P₁ (φ bz.1)) bz.2).left :=
    LocLift.isHolTo_comp (β := fun bz : V × (Fin g → ℂ) => (φ bz.1, bz.2)) (Fu.hol i _ B₁ P₁ hB₁ hP₁).2
      (hB'.prod isOpen_univ) (by fun_prop) fun _ h => ⟨h.1, trivial⟩
  choose! w M hM hw using fun b (hb : b ∈ φ ⁻¹' B₁) =>
    exists_dirs Fu (a b) (y b) (hy b (hsub' hb)) i (P₁ (φ b)) (hP₁.1 _ hb) (hu b hb)
  have hM' : ∀ b ∈ φ ⁻¹' B₁, M b * (Matrix.of fun i j => w b j i) = 1 := fun b hb => by
    ext i j
    have := congrFun (hM b hb j) i
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  let Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ)) := fun b =>
    AddMonoidHom.mk' (fun v z => (M b *ᵥ P₁ (φ b) v) (e.symm z)) fun v v' => by
      funext z
      simp [Matrix.mulVec_add]
  refine ⟨φ ⁻¹' B₁, i, Q, hB', hb₁, hsub', fun b hb => ⟨P₁ (φ b), fun z => w b (e.symm z), y b, hP₁.1 _ hb,
    (hu b hb).symm, hy b (hsub' hb), hw b hb, fun v => ?_⟩, fun v z b hb => ?_⟩
  · have h1 := congrArg (· *ᵥ P₁ (φ b) v) (mul_eq_one_comm.1 (hM' b hb))
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm fun j => (M b *ᵥ P₁ (φ b) v) j • w b j).symm
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  · have hwd : ∀ j, DifferentiableAt ℂ (fun b => w b j) b := fun j => by
      obtain ⟨z, rfl⟩ := e.symm.surjective j
      refine differentiableAt_dir Z.m0.toSABMap.cart.1 Z.m.cart.1 (LocLift.isHolTo_mono hyh hB' hsub')
        (ex := fun b u => (Fu.ex i (P₁ (φ b)) u).left) hex
        (fun b hb u => (Over.w (Fu.ex i (P₁ (φ b)) u)).trans (hu b hb)) hb (fun u h => ?_)
        (v := fun b => (a b).2.v z.1 z.2) (fun U f => (ha.2 z.1 z.2 U f).mono fun _ h => ⟨hsub' h.1, h.2⟩)
        fun b hb => hw b hb z
      have h0 : IsDerivAt (fun u => (Fu.ex i (P₁ (φ b)) u).left) 0 0 (constVec (Fu.ex i (P₁ (φ b)) 0).left) :=
        (isDerivAt_constVec_iff (c := fun u => (Fu.ex i (P₁ (φ b)) u).left)).2 fun _ _ _ => map_zero _
      exact ((Fu.ex_diff i _ (hP₁.1 _ hb)).2 (Over.homMk _ h.over) h.1).unique ((isDerivAt0_iff _ _ _).2 h)
        ((isDerivAt0_iff _ _ _).2 h0)
    have hMd : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b :=
      HolFrameMatrix.differentiableAt_of_mul_eq_one M (fun b => Matrix.of fun i j => w b j i) b
        (fun i j => differentiableAt_pi.1 (hwd j) i) (eventually_of_mem (hB'.mem_nhds hb) hM')
    have hPd : DifferentiableAt ℂ (fun b => P₁ (φ b) v) b :=
      ((hP₁.2 v).differentiableAt (hB₁.mem_nhds hb)).comp b φ.differentiableAt
    refine DifferentiableAt.differentiableWithinAt ?_
    show DifferentiableAt ℂ (fun b => ∑ j, M b (e.symm z) j * P₁ (φ b) v j) b
    exact DifferentiableAt.fun_sum fun j _ => (hMd _ j).mul (differentiableAt_pi.1 hPd j)

end GlobalTheory.ShFam.HorLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}

section Directions

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1)
  (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ))

include hP hu hy hW in

theorem dirs_exists_comb (τ : E →+* ℂ) (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • W ⟨τ, k⟩ := by
  choose v₀ h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 w
  have ht := t1 w v hv
  have he := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP w v τ hv).2 hw
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [ht.1, ← hu, Category.assoc])
  obtain ⟨cf, hcf, -⟩ := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hu k1).1 ht))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1 (he b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hcf
  have hc := (comb_iff Z.m0.toSABMap hu (fun k => h1 ⟨τ, k⟩) cf k1).2 ((comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf k1).1 hcf)
  exact ⟨cf, (t3 _ ht).unique hv ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _
    (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).1 hc)⟩

include hP hu hy hW in

theorem dirs_span : ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨cf, h⟩ := dirs_exists_comb hP hu hy hW (e j).1 (Pi.basisFun ℂ (Fin g) j) fun k hk => by
    by_contra hne
    exact hk (by rw [Pi.basisFun_apply]; exact Pi.single_eq_of_ne (fun h => hne (by rw [h])) _)
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

include hP hu hy hW in

theorem dirs_basis : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W :=
  ⟨basisOfTopLeSpanOfCardEqFinrank W (dirs_span hP hu hy hW) (by
    rw [Module.finrank_fin_fun, ← Fintype.card_congr e, Fintype.card_fin]), coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Directions

theorem Inner.exists_lift {x : CxPts (genStr Z) σ} (h : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  have hr : Set.range x.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact not_not.1 h
  exact ⟨IsOpenImmersion.lift Z.jQ _ hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_dirs (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) :
    ∃ W : Letter Dw → Fin g → ℂ, ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  choose v₀ h1 h2 using fun z : Letter Dw => exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) (a.2.v z.1 z.2)
    (by rw [(a.2.tan z.1 z.2).1, ← hx, Category.assoc])
  choose W hW using fun z : Letter Dw => ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hu (h1 z)).2 ((tan_iff Z.m hx (h1 z)).1 (h2 z ▸ a.2.tan z.1 z.2)))).exists
  exact ⟨W, fun z => ⟨v₀ z, h1 z, h2 z, hW z⟩⟩

theorem exists_per_of_isPeriod (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) : ∃ Q, Per Fu a i Q := by
  obtain ⟨W, hW⟩ := exists_dirs hP hu hy
  obtain ⟨b, rfl⟩ := dirs_basis hP hu hy hW
  exact ⟨b.equivFun.toLinearMap.toAddMonoidHom.comp P, P, b, y, hP, hu, hy, hW, fun v => (b.sum_equivFun (P v)).symm⟩

theorem exists_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a ha
  obtain ⟨y, hy⟩ := ha.exists_lift
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact a.1.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  exact ⟨i, exists_per_of_isPeriod hP hu.symm hy⟩

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbedding
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  GlobalTheory.LieMet GlobalTheory.DRFlag
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono
  le_preimage_comp ext_ev)

namespace GlobalTheory.DRFlag

variable {Z : Scheme.{0}}

theorem exists_ev_eq_pow_mul {U W : Z.Opens} (hU : IsAffineOpen U) (f : Γ(Z, U)) (hW : Z.basicOpen f = W)
    (x : Γ(Z, W)) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ y : Γ(Z, U), ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z)
      (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z ⁻¹ᵁ W), ev z U h y = ev z U h f ^ n * ev z W h' x := by
  subst hW
  obtain ⟨n₀, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z U hU f x
  refine ⟨n₀, fun n hn => ⟨f ^ (n - n₀) * y, fun S _ z h h' => ?_⟩⟩
  have e : resG Z (Z.basicOpen_le f) y = resG Z (Z.basicOpen_le f) f ^ n₀ * x := hy
  have e' := congrArg (ev z _ h') e
  rw [map_mul, map_pow, ev_res z _ h' h, ev_res z _ h' h] at e'
  rw [map_mul, map_pow, e', ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

theorem exists_pow_mul_eq_of_ev {U : Z.Opens} (hU : IsAffineOpen U) (f x y : Γ(Z, U))
    (H : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ U), ⊤ ≤ z ⁻¹ᵁ Z.basicOpen f →
      ev z U h x = ev z U h y) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → f ^ n * x = f ^ n * y := by
  have e : resG Z (Z.basicOpen_le f) (x - y) = 0 := ext_ev fun S _ z hz => by
    have h := le_preimage_mono (Z.basicOpen_le f) hz
    rw [ev_res z _ hz h, map_sub, map_zero, H S z h hz, sub_self]
  obtain ⟨n₀, hn₀⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Z hU (x - y) f e
  refine ⟨n₀, fun n hn => ?_⟩
  rw [← sub_eq_zero, ← mul_sub, ← Nat.sub_add_cancel hn, pow_add, mul_assoc, hn₀, mul_zero]

theorem Coc.exists_emb_of_ratio (C : Coc Z) [Finite C.A] (r : ∀ d : C.A, C.A → Γ(Z, C.B d))
    (hb : ∀ d g, Z.basicOpen (r d g) = C.B d ⊓ C.B g) (hs : ∀ d, r d d = 1)
    (hm : ∀ (d e g : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
      ev z _ hd (r d e) * ev z _ he (r e g) = ev z _ hd (r d g)) : ∃ N, Nonempty (C.Emb N) := by
  classical
  have := Fintype.ofFinite C.A
  choose m₀ hm₀ using fun p : Σ g : C.A, Σ d : C.A, Fin (C.n g) × Fin (C.n d) =>
    exists_ev_eq_pow_mul (C.aff p.2.1) (r p.2.1 p.1) ((hb _ _).trans (inf_comm _ _)) (C.T p.1 p.2.1 p.2.2.1 p.2.2.2)
  obtain ⟨m, hmm⟩ : ∃ m, ∀ p, m₀ p ≤ m := ⟨Finset.univ.sup m₀, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  choose Y₀ hY₀ using fun p => hm₀ p m (hmm p)
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ g d : C.A, Matrix (Fin (C.n g)) (Fin (C.n d)) Γ(Z, C.B d),
      ∀ g d (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hg : ⊤ ≤ z ⁻¹ᵁ C.B g) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d),
        (Y g d).map (ev z _ hd) = ev z _ hd (r d g) ^ m • C.tr g d z hg hd :=
    ⟨fun g d => Matrix.of fun i j => Y₀ ⟨g, d, i, j⟩, fun g d S _ z hg hd => Matrix.ext fun i j =>
      hY₀ ⟨g, d, i, j⟩ S z hd (le_preimage_inf hg hd)⟩
  have hY1 : ∀ g, Y g g = 1 := fun g => Matrix.ext fun i j => ext_ev fun S _ z hz => by
    have e := hY g g S z hz hz
    rw [hs, map_one, one_pow, one_smul, C.tr_self] at e
    exact (congrFun (congrFun e i) j).trans
      (congrFun (congrFun (Matrix.map_one _ (map_zero (ev z _ hz)) (map_one _)) i) j).symm
  have key : ∀ g d e, ∀ i j, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z)
      (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
      ev z _ hd (r d g) ^ n * ((Y g d).map (ev z _ hd) * C.tr d e z hd he) i j =
        ev z _ hd (r d g) ^ n * (ev z _ hd (r d e) ^ m * ev z _ he (Y g e i j)) := by
    intro g d e i j
    have ha : IsAffineOpen (C.B d ⊓ C.B e) := hb d e ▸ (C.aff d).basicOpen (r d e)
    have e₁ : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
        ev z _ (le_preimage_inf hd he) (((Y g d).map (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d)) * C.T d e) i j) =
          ((Y g d).map (ev z _ hd) * C.tr d e z hd he) i j := fun S _ z hd he => by
      rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Matrix.map_apply, ev_res z _ _ hd]
      rfl
    have e₂ : ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hd : ⊤ ≤ z ⁻¹ᵁ C.B d) (he : ⊤ ≤ z ⁻¹ᵁ C.B e),
        ev z _ (le_preimage_inf hd he) (resG Z inf_le_left (r d e) ^ m * resG Z inf_le_right (Y g e i j)) =
          ev z _ hd (r d e) ^ m * ev z _ he (Y g e i j) := fun S _ z hd he => by
      rw [map_mul, map_pow, ev_res z _ _ hd, ev_res z _ _ he]
    obtain ⟨n₀, hn₀⟩ := exists_pow_mul_eq_of_ev ha (resG Z inf_le_left (r d g))
      (((Y g d).map (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d)) * C.T d e) i j)
      (resG Z inf_le_left (r d e) ^ m * resG Z inf_le_right (Y g e i j)) fun S _ z h h' => by
        have hd := le_preimage_mono inf_le_left h
        have he := le_preimage_mono inf_le_right h
        have hle : Z.basicOpen (resG Z (inf_le_left : C.B d ⊓ C.B e ≤ C.B d) (r d g)) ≤ C.B g :=
          (Z.basicOpen_res (r d g) (homOfLE inf_le_left).op).le.trans
            (inf_le_right.trans ((hb d g).le.trans inf_le_right))
        have hg := le_preimage_mono hle h'
        refine (e₁ S z hd he).trans (Eq.trans ?_ (e₂ S z hd he).symm)
        have e₃ : ev z _ he (Y g e i j) = ev z _ he (r e g) ^ m * C.tr g e z hg he i j :=
          congrFun (congrFun (hY g e S z hg he) i) j
        rw [hY g d S z hg hd, Matrix.smul_mul, C.tr_mul, e₃, ← mul_assoc, ← mul_pow, hm]
        rfl
    refine ⟨n₀, fun n hn S _ z hd he => ?_⟩
    have e₄ := congrArg (ev z _ (le_preimage_inf hd he)) (hn₀ n hn)
    rwa [map_mul, e₁ S z hd he, map_mul, e₂ S z hd he, map_pow, ev_res z _ _ hd] at e₄
  choose n₀ hn₀ using fun p : Σ g : C.A, Σ _ : C.A, Σ e : C.A, Fin (C.n g) × Fin (C.n e) =>
    key p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  obtain ⟨n, hn⟩ : ∃ n, ∀ p, n₀ p ≤ n := ⟨Finset.univ.sup n₀, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  let q : Option (Σ g : C.A, Fin (C.n g)) ≃ Fin (Fintype.card (Σ g : C.A, Fin (C.n g)) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  let A : ∀ d, Option (Σ g : C.A, Fin (C.n g)) → Fin (C.n d) → Γ(Z, C.B d) := fun d o j =>
    o.elim 0 fun p => r d p.1 ^ n * Y p.1 d p.2 j
  refine ⟨_, ⟨⟨fun d => Matrix.of fun k j => A d (q.symm k) j,
    fun d => ⟨Matrix.of fun i k => if k = q (some ⟨d, i⟩) then 1 else 0, Matrix.ext fun i j => ?_⟩,
    fun d e S _ z hd he => ?_⟩⟩⟩
  · simp [Matrix.mul_apply, A, hs, hY1]
  · have hu : IsUnit (ev z _ hd (r d e)) := IsUnit.of_mul_eq_one _ ((hm d e d S z hd he).trans (by rw [hs, map_one]))
    refine ⟨hu.unit ^ (m + n), Matrix.ext fun k j => ?_⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec, smul_eq_mul]
    rcases q.symm k with _ | ⟨g, i⟩
    · simp [A]
    · have e₅ := hn₀ ⟨g, d, e, i, j⟩ n (hn _) S z hd he
      simp only [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, ← mul_assoc] at e₅
      simp only [A, Option.elim_some, map_mul, map_pow]
      rw [e₅, ← hm d e g S z hd he]
      ring

theorem Coc.exists_refine_emb : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Z : Scheme.{0}) (s : Z ⟶ Sp O),
    IsProjOver s → ∀ C : Coc Z, ∃ (Γ : Type) (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ g, IsAffineOpen (D g))
      (cover : ∀ x : Z, ∃ g, x ∈ D g) (le : ∀ g, D g ≤ C.B (a g)) (N : ℕ),
      Nonempty ((C.refine a D aff cover le).Emb N) := by
  intro O _ _ Z s hZ C
  classical
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isProjOver hZ
  have := hL.compactSpace
  choose a ha using C.cover
  choose n hn t hx hle haff using fun x => hL.exists_affine_le (ha x)
  obtain ⟨F, hF⟩ := (isCompact_univ (X := Z)).elim_finite_subcover
    (fun x => (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t x) : Set Z)) (fun x => (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t x)).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  have hd : ∀ g : F, ∃ u : (lbPow L (∏ x ∈ F, n x)).Sec,
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t g.1) := fun g => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n g.2
    have hk0 : 1 ≤ k := Nat.pos_of_ne_zero fun h => (Finset.prod_pos fun x _ => hn x).ne' (by rw [hk, h, mul_zero])
    exact ⟨secCast hk.symm (secPow (t g.1) k), (nonzeroLocus_secCast _ _).trans (nonzeroLocus_secPow _ hk0)⟩
  choose u hu using hd
  have cover : ∀ x : Z, ∃ g, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (u g) := fun x => by
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, (hu ⟨y, hy⟩).ge h⟩
  refine ⟨F, fun g => a g.1, fun g => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (u g), fun g => (congrArg IsAffineOpen (hu g)).mpr (haff g.1), cover,
    fun g => (hu g).le.trans (hle g.1), ?_⟩
  refine @Coc.exists_emb_of_ratio Z _ (inferInstanceAs (Finite F)) (fun d g => ProjSpace.secRatio (u d) (u g))
    (fun d g => ProjSpace.basicOpen_secRatio _ _) (fun d => ProjSpace.secRatio_self _) fun d e g S _ z hd he => ?_
  have h := congrArg (ev z _ (le_preimage_inf hd he))
    (ProjSpace.secRatio_mul_secRatio (u d) (u e) (u g) inf_le_left inf_le_right)
  exact ((congrArg₂ (· * ·) (ev_res z _ _ hd _) (ev_res z _ _ he _)).symm.trans
    ((map_mul _ _ _).symm.trans h)).trans (ev_res z _ _ hd _)

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ), (∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) → rootDiscr m ∣ P := by
  first | exact @GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | exact GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | (intros; apply GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZeroStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  first | exact @GlobalTheory.GoodMetric.rootDiscr_ne_zero | exact GlobalTheory.GoodMetric.rootDiscr_ne_zero | (intros; apply GlobalTheory.GoodMetric.rootDiscr_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPermStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  first | exact @GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | exact GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | (intros; apply GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChooseStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_space_dimension_eq_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  first | exact @GlobalTheory.FlagDimSum.dim_add_sum_choose | exact GlobalTheory.FlagDimSum.dim_add_sum_choose | (intros; apply GlobalTheory.FlagDimSum.dim_add_sum_choose <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
section
set_option autoImplicit false

noncomputable section

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePairGram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def ent (M : Matrix (Fin r) (Fin r) ℂ) (a b : ℕ) : ℂ := if h : a < r ∧ b < r then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

open Classical in

def coef (X : Data E r) (x x' : Frame X.Ψ r) (ρ : E →+* ℂ) (b i : ℕ) : ℂ :=
  if h : ρ ∈ X.Ψ then ent ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) (X.p0 + b) (X.p0 + i)
  else if h' : conjEmb ρ ∈ X.Ψ then ent ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) (X.p0 - 1 - i) (X.p0 - 1 - b)
  else 0

example (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom) (ρ : X.Ψ) (b i : ℕ) (hb : X.p0 + b < r) (hi : X.p0 + i < r) :
    coef X x x ρ.1 b i = if b = i then 1 else 0 := by
  have hd : IsUnit (mat x ρ).det := (hx ρ).1.isUnit
  simp only [coef, dif_pos ρ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, nonsing_inv_mul _ hd, one_apply,
    Fin.mk.injEq, Nat.add_left_cancel_iff]

end GlobalTheory.FramePairGram
end
end

