import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {x0 : Sp S ⟶ Xo.X} {x0' : Sp S' ⟶ Xo.X}
  (hx : x0' = spMap ψ ≫ x0)

def jbc (d m n : ℕ) : overAt x0' (Jet S' (Fin n × Fin d) m) ⟶ overAt x0 (Jet S (Fin n × Fin d) m) :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by subst hx; exact Over.w (rjBC ψ x0 d m n))

def bcB : overAt x0' S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    subst hx
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap])

def bcD : overAt x0' (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    subst hx
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

include hx in
theorem isCombAt_bc {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt x0' (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => bcD ψ hx ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap, Category.assoc]
  · have e : List.ofFn (fun i => bcD ψ hx ≫ u i) = (List.ofFn u).map (bcD ψ hx ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridge
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def idIso {Y : Scheme.{0}} (M : LB Y) : LB.Iso M M := ⟨fun p => M.g p.1 p.2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Gx

variable {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X)

def gxLift {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    Z ⟶ Gx x :=
  (lift (Over.homMk a rfl : Over.mk (a ≫ x) ⟶ Over.mk x) (Over.homMk b w : Over.mk (a ≫ x) ⟶ Xo.univ.t.G)).left

theorem gxLift_fst {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (fst (Over.mk x) Xo.univ.t.G).left = a := by
  rw [gxLift, ← Over.comp_left, lift_fst] <;> rfl

theorem gxLift_snd {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (snd (Over.mk x) Xo.univ.t.G).left = b := by
  rw [gxLift, ← Over.comp_left, lift_snd] <;> rfl

theorem gx_ext {Z : Scheme.{0}} (p q : Z ⟶ Gx x)
    (h1 : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h2 : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left) : p = q := by
  have e : (Over.mk x ⊗ Xo.univ.t.G).hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have hw : q ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    rw [e, ← Category.assoc, ← h1, Category.assoc]
  let P : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk p rfl
  let Q : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk q hw
  have hPQ : P = Q := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [P, Q] using h1
    · ext
      simpa [P, Q] using h2
  have := congrArg (fun f => f.left) hPQ
  simpa [P, Q] using this

theorem gx_w : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x := by
  exact (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm

def gxU : pullback Xo.univ.t.G.hom x ⟶ Gx x := gxLift x (pullback.snd _ _) (pullback.fst _ _) pullback.condition

def gxV : Gx x ⟶ pullback Xo.univ.t.G.hom x :=
  pullback.lift (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (gx_w x)

theorem gxU_fst : gxU x ≫ (fst (Over.mk x) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst x _ _ _
theorem gxU_snd : gxU x ≫ (snd (Over.mk x) Xo.univ.t.G).left = pullback.fst _ _ := by
  exact gxLift_snd x _ _ _
theorem gxV_fst : gxV x ≫ pullback.fst _ _ = (snd (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_fst _ _ _
theorem gxV_snd : gxV x ≫ pullback.snd _ _ = (fst (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem gxU_gxV : gxU x ≫ gxV x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, gxV_fst, gxU_snd, Category.id_comp]
  · rw [Category.assoc, gxV_snd, gxU_fst, Category.id_comp]

theorem gxV_gxU : gxV x ≫ gxU x = 𝟙 _ := by
  apply gx_ext x
  · rw [Category.assoc, gxU_fst, gxV_snd, Category.id_comp]
  · rw [Category.assoc, gxU_snd, gxV_fst, Category.id_comp]

theorem gs_scal (a : S) (i : Fin 1 → Xo.univ.t.PP.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z)
    (hz : r z ∈ (PPx x).U i) :
    gs r z ((PPx x).U i) (scal x a i) = cst (r ≫ (fst (Over.mk x) Xo.univ.t.G).left) z a := by
  exact (gs_res r z le_top hz _).trans (gs_pull r _ z ⊤ trivial _)

theorem scal_eq_iff (s t : LB.Sec (PPx x)) (a : S) :
    (∀ i, s.f i = scal x a i * t.f i) ↔ ∀ i, ∀ y ∈ (PPx x).U i,
      gs (𝟙 _) y _ (s.f i) = cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs (𝟙 _) y _ (t.f i) := by
  constructor
  · intro h i y hy
    rw [h i, gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
  · intro h i
    apply fn_ext
    intro y hy
    rw [gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
    exact h i y hy

end Gx

section BC

variable {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem bcU_w : (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ pullback.fst Xo.univ.t.G.hom x) ≫
    Xo.univ.t.G.hom = pullback.snd (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ spMap ψ ≫ x := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

def bcU : pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ⟶ Gx (spMap ψ ≫ x) :=
  gxLift (spMap ψ ≫ x) (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst _ _) (bcU_w ψ x)

theorem bcV_w : (bcPm ψ x ≫ gxV x) ≫ pullback.snd Xo.univ.t.G.hom x =
    (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Category.assoc, gxV_snd, bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl

def bcV : Gx (spMap ψ ≫ x) ⟶ pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) :=
  pullback.lift (bcPm ψ x ≫ gxV x) (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left (bcV_w ψ x)

theorem bcU_fst : bcU ψ x ≫ (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst _ _ _ _
theorem bcU_snd : bcU ψ x ≫ (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left =
    pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x := by
  exact gxLift_snd _ _ _ _
theorem bcV_fst : bcV ψ x ≫ pullback.fst _ _ = bcPm ψ x ≫ gxV x := by
  exact pullback.lift_fst _ _ _
theorem bcV_snd : bcV ψ x ≫ pullback.snd _ _ = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem bcV_snd' : bcV ψ x ≫ pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x =
    (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_fst, hbs]

theorem bcV_bcU : bcV ψ x ≫ bcU ψ x = 𝟙 _ := by
  apply gx_ext (spMap ψ ≫ x)
  · rw [Category.assoc, bcU_fst, bcV_snd, Category.id_comp]
  · rw [Category.assoc, bcU_snd, bcV_snd', Category.id_comp]

theorem bcU_bcPm : bcU ψ x ≫ bcPm ψ x = pullback.fst _ _ ≫ gxU x := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  have hbf : bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left
      = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
    rw [bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl
  apply gx_ext x
  · rw [Category.assoc, hbf, ← Category.assoc, bcU_fst, Category.assoc, gxU_fst, pullback.condition]
  · rw [Category.assoc, hbs, bcU_snd, Category.assoc, gxU_snd]

theorem bcU_bcV : bcU ψ x ≫ bcV ψ x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcV_fst, ← Category.assoc, bcU_bcPm, Category.assoc, gxU_gxV,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, bcV_snd, bcU_fst, Category.id_comp]

theorem bcV_gxU : bcV ψ x ≫ pullback.fst _ _ ≫ gxU x = bcPm ψ x := by
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_gxU, Category.comp_id]

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def PlaceIntegralUnramified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      0 ≤ vAtV y f

def PlaceBoundOwnPrime : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      ((D.host.pde : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (D.host.pde : T.Q.c.F) : ℤ) : ℝ) *
          ((DF w : ℝ) + 2 * D.R.f * D.R.r * w.n))) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundTwo : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundOddRamified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (p : ℕ), p ∈ ({D.host.q, D.host.d} : Finset ℕ) →
      ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤
        vAtV y f

def PlaceBoundSplitPrime : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (i : Fin 2) (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      (((-(((vLa la (embK T.Q.c τ πE) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aP t k : ℕ) : ℝ) +
          ((vLa la (embK T.Q.c τ (T.Q.H.bar πE)) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aM t k : ℕ) : ℝ))) : ℝ) : EReal) ≤
        vAtV y f

def WeightAssemblyClause : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (wL : WeightFamilies.Wt D j),
    S.sW ≠ 0 → LastPos (T.Q.Dw j) (wtA wL) →
    (∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la) (g : T.R j), g ∈ T.th j wL →
      (((-(((vLa la ((S.sW : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ))) : ℝ) : EReal) ≤ vAtV y g) →
    (recPJ h j hj).WWc S.sW wL ≤ (recB h.toLawsCore).Mlat j wL

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem readings_holomorphic_cuspForms (hM5 : SiegelSpaceAlgebra (E := E)) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : RdHolCusp σ (laU (U σ) a n) (rdC U σ a n) := by
  intro f
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  have hf : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := h2 hσ
  let K : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | IsHolCusp (U σ).X (laU (U σ) a n) P}
      zero_mem' := by
        intro k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).1
      add_mem' := by
        intro P Q hP hQ k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.1 _ (hP k) _ (hQ k)
      smul_mem' := by
        intro z P hP k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.2 z _ (hP k) }
  have hle : holSub (U σ).X (laU (U σ) a n) ≤ K := Submodule.span_le.mpr (fun P hP => hP)
  exact hle hf

theorem rdC_mem_holSub {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := by
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  exact h2 hσ

theorem rdC_mem_holSub0 {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub0 (U σ).X (laU (U σ) a n) := by
  refine Submodule.mem_inf.mpr ⟨rdC_mem_holSub hσ a n f, ?_⟩
  intro k x hx
  simp [rdC, rdU, hx]

end Read

def JInjAt {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hd : Dom a n) : Prop :=
  JInj (T.V j T.σ₀) T.σ₀ (rdC (T.U j) T.σ₀ a n) (T.dict j T.σ₀) (T.mu j T.σ₀) (h.cuspidalL2Subspace j hj T.σ₀ T.good_σ₀ a n hd)

def JInjRd {D : D7} (T : Top D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  IndepToC (rdC (T.U j) T.σ₀ a n)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def netNorm (U : Unf Xo c σ r) (la : ∀ k, Wt (U.X k).Ψ r) (NN : Finset (FPt U.X)) (P : FDSec U.X) : ℝ :=
  Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, ((U.X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)

def NnOf (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) (f : Rul Xo c) : ℝ :=
  dmet n (Module.finrank ℚ E / 2) r * netNorm U (laU U a n) NN (rdU U f)

def IsNet (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) : Prop :=
  NN.Nonempty ∧ ∀ P ∈ holSub U.X (laU U a n),
    supN U.X (laU U a n) P ≤ 4 * Real.sqrt NN.card * netNorm U (laU U a n) NN P

def NetExistsSt : Prop :=
  ∃ Cn : ℝ, ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → SupBoundPageRows D large₂ ka →
    ∃ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN ∧
      Real.log (16 * NN.card) ≤ Cn * Zb D large₂ ^ 3

def AlgInjAtSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (m : ℕ) (f : Fin m → T.C j ka),
      LinearIndependent T.Q.c.F f → LinearIndependent ℂ (fun i => rdU (T.U j σ) (f i : T.R j))

def NnLawsSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    (∀ f ∈ T.C j ka, 0 ≤ NnOf (T.U j σ) (wtA ka) ka.n NN f) ∧
    (∀ f ∈ T.C j ka, NnOf (T.U j σ) (wtA ka) ka.n NN f = 0 → f = 0) ∧
    (∀ (x : T.Q.c.F), ∀ f ∈ T.C j ka,
      NnOf (T.U j σ) (wtA ka) ka.n NN (x • f) = ‖σ x‖ * NnOf (T.U j σ) (wtA ka) ka.n NN f) ∧
    (∀ f ∈ T.C j ka, ∀ g ∈ T.C j ka,
      NnOf (T.U j σ) (wtA ka) ka.n NN (f + g) ≤
        NnOf (T.U j σ) (wtA ka) ka.n NN f + NnOf (T.U j σ) (wtA ka) ka.n NN g) ∧
    (∀ f ∈ T.C j ka, NnOf (T.U j σ) (wtA ka) ka.n NN f ≤ supNU (T.U j σ) (wtA ka) ka.n f)

def SupNormFromNet : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    ∀ f ∈ T.C j ka, supNU (T.U j σ) (wtA ka) ka.n f ^ 2 ≤ 16 * NN.card * NnOf (T.U j σ) (wtA ka) ka.n NN f ^ 2

def LogDFromNetSt : Prop :=
  AlgInjAtSt →
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN →
    Module.finrank T.Q.c.F (T.C j ka) ≤ NN.card

def HermFromNetSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (NN : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Finset (FPt (T.U j σ).X)),
    (∀ σ (hσ : GoodEmb T.Q.c σ), IsNet (T.U j σ) (wtA ka) ka.n (NN σ hσ)) →
    ∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm
        (fun σ (f : T.C j ka) => NnOf (T.U j (goodOf T.Q.c σ)) (wtA ka) ka.n
          (NN (goodOf T.Q.c σ) (goodEmb_goodOf T.Q.c σ)) (f : T.R j)) dH), Hm.Conj

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ThetaValCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
    TorusPins W Wu A L →
    ∀ (x2 : Fin w.n → (T.Q.Dw j).La),
      (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      (∀ b, x2 b - x b ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf)) =
        ((T.Q.l.M : ℂ)⁻¹) ^ P.totalDegree *
          star (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.map ((starRingEnd ℂ).comp σ) P)
            (fun l => Pi.single l.2.2 (L (Pi.single (W.e.symm ⟨l.1, l.2.1⟩) 1)))
            (A.T.U (T.Q.l.M ^ 2) (fun b => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) • L (star (W.Pm (W.F.t (W.ik k) (x2 b))))))
              (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

