import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem chart_iff {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (q : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) :
    ⊤ ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ (q ≫ gxFst x) ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  constructor
  · intro hp
    exact Set.mem_iInter.1 hp (0 : Fin 1)
  · intro hp
    exact Set.mem_iInter.2 fun _ => hp

theorem exists_pt {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (s : Sp ℂ ⟶ Sp R) (p : Sp ℂ ⟶ Xo.univ.t.G.left)
    (h : s ≫ x = p ≫ Xo.univ.t.G.hom) : ∃ q : Sp ℂ ⟶ Gx x, q ≫ gxFst x = p ∧ q ≫ gxSnd x = s :=
  ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) s p h, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem val_pull {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X) (x : Sp ℂ ⟶ Xo.X)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀) (h₁ : pm ≫ gxFst x₀ = gxFst x)
    (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx x) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst x)
    (e₂ : pt ≫ gxSnd x = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U i) :
    valAt' pt ((PPx x).U i) (s.f i) = valAt' q ((PPx x₀).U i) (s₀.f i) := by
  have hq : q = pt ≫ pm := SecCalc.pm_ext _ _
    (e₁.trans (show pt ≫ gxFst x = (pt ≫ pm) ≫ gxFst x₀ by rw [Category.assoc, h₁]))
    (e₃.trans (show spMap φ = (pt ≫ pm) ≫ gxSnd x₀ by
      rw [Category.assoc, h₂, ← Category.assoc, e₂, Category.id_comp]))
  rw [← h₃ i (SecCalc.ppx_le pm h₁ i), hq]
  exact valAt'_appLE pt pm _ _ _ _ hp

theorem val_mul_pull (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (a : ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x y : Sp ℂ ⟶ Xo.X) (hxy : y = x)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (t : LB.Sec (PPx y)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hst : SecBC (RingHom.id ℂ) a x y s t)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx y) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst y)
    (e₂ : pt ≫ gxSnd y = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i) :
    valAt' pt ((PPx y).U i) (t.f i) = a * valAt' q ((PPx x₀).U i) (s₀.f i) := by
  subst hxy
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [SecCalc.spMap_id', Category.id_comp]
  have ht := ((SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ _ _ y y y hy hy).2.1 a s t).1 hst i
  rw [ht, (sec_values_complex_fibre hT E H Dw l Xo y s).1 a i pt e₂,
    val_pull φ x₀ y s₀ s pm h₁ h₂ h₃ i pt q e₁ e₂ e₃ hp]

theorem exists_val_ne (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x u : Sp ℂ ⟶ Xo.X) (hu : u = x) (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hs : SecGen x s) :
    ∃ (e : Over.mk u ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι), ∀ q : Sp ℂ ⟶ Gx x₀, q ≫ gxFst x₀ = e.left →
      q ≫ gxSnd x₀ = spMap φ → valAt' q ((PPx x₀).U (fun _ => j)) (s₀.f (fun _ => j)) ≠ 0 := by
  subst hu
  obtain ⟨i, pt, hpt, hv⟩ := (sec_values_complex_fibre hT E H Dw l Xo u s).2.1.1 hs
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k : Fin 1 => congrArg i (Subsingleton.elim _ _)⟩
  have hc : gxSnd u ≫ u = gxFst u ≫ Xo.univ.t.G.hom := pullback.condition (f := u) (g := Xo.univ.t.G.hom)
  refine ⟨Over.homMk (pt ≫ gxFst u) ?_, j, fun q e₁ e₃ => ?_⟩
  · show (pt ≫ gxFst u) ≫ Xo.univ.t.G.hom = u
    rw [Category.assoc, ← hc, ← Category.assoc, hpt, Category.id_comp]
  · rw [← val_pull φ x₀ u s₀ s pm h₁ h₂ h₃ _ pt q e₁ hpt e₃ (top_le_preimage_of_valAt'_ne_zero _ hv)]
    exact hv

end

theorem differentiableOn_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => toC (a b)) B := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hBd hψ hb hκ b₀ hb₀
  let φ : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hBd hb), fun x => (T.holPer.2 x).mono hBd⟩
  have hux : ∀ b ∈ B, F.u k (T.Pf (T.co b)) = (z b).x := fun b h =>
    (hb b h).2.2.1.symm.trans (hb b h).2.1.1
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).1.2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) y₀.x (z b₀).x _ (hux b₀ hb₀) y₀.s (z b₀).s pm₀ p₁ p₂ p₃ (z b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx y₀.x, q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx y₀.x, b ∈ B → q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd y₀.x) (gxFst y₀.x) y₀.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback y₀.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx y₀.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co b)) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m B T.h T.ta hB
    (fun b h => ⟨(T.norm b (hBd h)).2.1, (T.norm b (hBd h)).2.2.1⟩)
    (fun i i' => ⟨(T.hol i i').1.mono hBd, (T.hol i i').2.mono hBd⟩)
  have d₀ : DifferentiableOn ℂ κ W := hκ.mono fun b h => h.1
  have d₁ : DifferentiableOn ℂ (fun b => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      hθ hι.differentiableOn fun b h => ⟨h.1, trivial⟩
  have d₂ : DifferentiableOn ℂ (fun b => T.fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      (T.fr_hol j) hι.differentiableOn fun b h => ⟨hBd h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, κ b * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀) * T.fr j (b, w₀) =
      toC (a b) * valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) := fun b h => by
    obtain ⟨⟨-, -, pm, p₁, p₂, p₃⟩, ⟨hyz, -, hbc⟩, hyu, -, hth⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (T.Pf (T.co b)) w₀).left
      (((Category.id_comp _).trans hyu).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
    refine (hth j w₀ pt e₁ e₂ (m₂ b h)).symm.trans ?_
    refine val_mul_pull hT (φ b) (toC (a b)) y₀.x (z b).x (y b).x hyz y₀.s (z b).s (y b).s pm p₁ p₂ p₃ hbc _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)
    rw [e₁]
    exact m₂ b h
  have d : DifferentiableOn ℂ (fun b => toC (a b)) W := (((d₀.mul d₁).mul d₂).mul (d₃.inv vnz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (vnz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.HolGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_algebraMap_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : R ⊗[F] E) (hz : sigR R σ z = z) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = z := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have h : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := by simp [sigR]
      rw [h, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT z
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← TensorProduct.smul_tmul', ← ht, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_unit_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : (R ⊗[F] E)ˣ)
    (hz : sigR R σ (z : R ⊗[F] E) = z) :
    ∃ a : Rˣ, Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom a = z := by
  have hz' : sigR R σ ((z⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (z⁻¹ : (R ⊗[F] E)ˣ) := by
    apply z.isUnit.mul_left_cancel
    conv_lhs => rw [← hz, ← map_mul]
    simp
  obtain ⟨a, ha⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz
  obtain ⟨b, hb⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz'
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

theorem exists_root_of_norm_one {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ y, σ y ≠ y) (u : E) (hu : σ u * u = 1) : ∃ x : Eˣ, (x : E) = u * σ x := by
  by_cases h : 1 + u = 0
  · obtain ⟨y, hy⟩ := hne
    refine ⟨Units.mk0 (y - σ y) (sub_ne_zero.2 hy.symm), ?_⟩
    rw [Units.val_mk0, map_sub, hσ]
    linear_combination (y - σ y) * h
  · refine ⟨Units.mk0 (1 + u) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination - hu

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem isDetRoot_laws : ∀ (D : D7) (V : HSp D), (∀ g : GA D V, ∃ x, IsDetRoot V g x) ∧ (∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → ∃ a, x' = x * idF D a) ∧ (∀ γ ∈ GQ V, ∃ x : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom x)) ∧ ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x') := by
  intro D V
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  refine ⟨GlobalTheory.RecDict.exists_isDetRoot D V, ?_, ?_, ?_⟩
  · intro g x x' hx hx'
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, hσ, add_comm]
    unfold IsDetRoot at hx hx'
    obtain ⟨a, ha⟩ := exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x⁻¹ * x') (by
      apply (x.isUnit.map (sigR (AF D.host.F) D.sp.cm.sig)).mul_left_cancel
      apply x.isUnit.mul_left_cancel
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left, mul_left_comm, ← Units.val_mul, mul_inv_cancel_left]
      linear_combination (sigR (AF D.host.F) D.sp.cm.sig (x' : AE D)) * hx -
        (sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hx')
    refine ⟨a, ?_⟩
    unfold idF
    rw [ha, mul_inv_cancel_left]
  · intro γ hγ
    obtain ⟨γ', -, hγ'⟩ := hγ
    have hdet : (Formalism.L2.Theta.mt V γ).det = incA D (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
      rw [RingHom.map_det]
      congr 1
      exact congrArg Units.val hγ'.symm
    have hc : ∀ y, cA D (incA D y) = incA D (D.sp.cm.sig y) := by
      intro y; simp [cA, sigR, inclR]
    have hinj : Function.Injective (incA D) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
    have hu := det_conj_mul V γ
    rw [hdet, hc, ← map_mul, ← map_one (incA D)] at hu
    obtain ⟨x, hx⟩ := exists_root_of_norm_one (D.sp.cm.sig : D.host.E →+* D.host.E) hσ
      (GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm) _ (hinj hu)
    refine ⟨x, ?_⟩
    have key : incA D (x : D.host.E) = (Formalism.L2.Theta.mt V γ).det * cA D (incA D (x : D.host.E)) := by
      rw [hdet, hc, ← map_mul]
      exact congrArg _ hx
    unfold IsDetRoot
    rw [Units.coe_map]
    exact key
  · exact isDetRoot_mul V

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallClosedField

open Cardinal

theorem mk_le_of_denseRange {A C : Type} [MetricSpace C] (f : A → C) (hf : DenseRange f) :
    #C ≤ #A ^ ℵ₀ := by
  have h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := by
    intro x
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (hxy ▸ hs y)
  simpa using mk_le_of_injective hinj

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_small_closed_subfield {K C : Type} [Field K] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra K C] (hK : #K ≤ 𝔠)
    {x : K} (hx : 1 < ‖algebraMap K C x‖) :
    ∃ L : Subfield C, (∀ y : K, algebraMap K C y ∈ L) ∧ IsClosed (L : Set C) ∧ IsAlgClosed L ∧
      #L ≤ 𝔠 := by
  let A := algebraicClosure K C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : K, algebraMap K C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  refine ⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩
  have hA : #A ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)
  exact (power_le_power_right hA).trans continuum_power_aleph0.le

theorem exists_scf_isometry {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), ∀ x, ‖e x‖ = ‖x‖ := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩

theorem exists_extension_intO {V W C : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (g : V →+* intO C) (φ : V →+* W)
    (hg : Function.Injective g) (hφ : Function.Injective φ) (hf : φ.Finite) :
    ∃ g' : W →+* intO C, g'.comp φ = g ∧ Function.Injective g' := by
  letI : Algebra V W := φ.toAlgebra
  letI : Algebra V C := ((intO C).subtype.comp g).toAlgebra
  haveI : Module.Finite V W := hf
  have hgC : Function.Injective (algebraMap V C) := Subtype.val_injective.comp hg
  haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC
  let l : W →ₐ[V] C := IsAlgClosed.lift
  have hl : Function.Injective l := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, l.commutes] at ha
    exact (map_eq_zero_iff _ hgC).1 ha
  have hmem : ∀ a : W, l a ∈ intO C := by
    intro a
    have hO := normIntegers_integers C
    obtain ⟨q, hq, hqa⟩ := (Algebra.IsIntegral.isIntegral (R := V) a).map l
    let g₀ : V →+* normIntegers C := (algebraMap V C).codRestrict (normIntegers C) fun v =>
      mem_normIntegers_iff.2 (g v).2
    have hint : IsIntegral (normIntegers C) (l a) :=
      ⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩
    exact mem_normIntegers_iff.1 (hO.mem_of_integral hint)
  refine ⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩
  ext a
  exact l.commutes a

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem exists_embedding_and_extension :
    ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T p hp hfin hpm
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩
  · obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
      exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm
        (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
    haveI : Finite (ResidueField T.V) := hfin
    have hK : #T.Fr ≤ 𝔠 :=
      (IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans
        (mk_le_continuum_of_finite_residueField T.V)
    have hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖ := by
      rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
    obtain ⟨L, hKL, hcl, hac, hL⟩ := exists_small_closed_subfield hK hx
    letI : NontriviallyNormedField L :=
      { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
    haveI : CompleteSpace L := hcl.completeSpace_coe
    haveI : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
    let i : T.Fr →+* L := (algebraMap T.Fr C).codRestrict L hKL
    have hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖ := fun _ => rfl
    haveI : CharZero L := charZero_of_injective_ringHom i.injective
    have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
      rw [← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]
    obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL
    have hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
      rw [RingHom.comp_apply, he, hi]; exact (hC _).2 ⟨a, rfl⟩
    refine ⟨D, e.comp i, hle, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  · obtain ⟨g', hc, hinj⟩ := exists_extension_intO g φ hg hφ hf
    refine ⟨g', hc, hinj, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2)
      ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha
    have := hgm p hpm
    rw [← hc] at this
    exact this

end GlobalTheory.SmallClosedField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponentStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedFramedPoint_on_each_component : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∃ un, IsNormUn T un := by
  first | exact @GlobalTheory.FrameUnif.exists_isNormUn | exact GlobalTheory.FrameUnif.exists_isNormUn | (intros; apply GlobalTheory.FrameUnif.exists_isNormUn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGeneratesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreSectionNowhereZero_of_generates : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  first | exact @GlobalTheory.Frames.secNZ_of_secGen | exact GlobalTheory.Frames.secNZ_of_secGen | (intros; apply GlobalTheory.Frames.secNZ_of_secGen <;> assumption)
end

