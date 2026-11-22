import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem appLE_apply_congr {X Z : Scheme.{0}} {a c : Z ⟶ X} (e : a = c) (U : X.Opens) (W : Z.Opens)
    (h₁ : W ≤ a ⁻¹ᵁ U) (h₂ : W ≤ c ⁻¹ᵁ U) (s : Γ(X, U)) : (a.appLE U W h₁).hom s = (c.appLE U W h₂).hom s := by
  subst e; rfl

theorem unitAt_fnMap_of {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩

theorem norms_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (V' : Cover Y) (b : V'.X ⟶ V.X)
    (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G), V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π →
    g (genericPoint V'.G) = genericPoint V.G → ∀ (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L f a l → Norms V' (L.pull b hb) f a l := by
  intro F _ _ Y V V' b hb g hj hπ hg L f a l h
  obtain ⟨r, hr, hu, hc, hfin⟩ := h
  have hgη : g (genericPoint V'.G) ⤳ genericPoint V.G := specializes_of_eq hg
  set ψ := SmallSec.fnMap g hgη with hψ
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  obtain ⟨hη', e'⟩ := V'.φ_eq_fnMap
  have hφ : ∀ t, V'.φ t = ψ (V.φ t) := by
    intro t
    rw [e', e, ← ProjSpace.fnMap_comp g V.π hgη hη (ProjSpace.comp_genericPoint_specializes _ _ hgη hη) t]
    exact ProjSpace.fnMap_congr hπ.symm _ _ _
  have hπx : ∀ x, V.π (g x) = V'.π x := fun x => by rw [← hπ]; rfl
  have hch : ∀ (i : ((L.pull b hb).B.pull V'.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V'.j).U i,
      g x ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L.B b V'.j i hx) PUnit.unit
    have h2 : (V'.j ≫ b) x = V.j (g x) := by rw [hj]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show V.j (g x) ∈ L.B.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull b hb).B.pull V'.j).ι → V'.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V'.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h0 : genericPoint V.G ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit) := by
      rw [← hg]
      exact ⟨hch i _ hij.1, hch j _ hij.2⟩
    have le : ((L.pull b hb).B.pull V'.j).U i ⊓ ((L.pull b hb).B.pull V'.j).U j ≤
        g ⁻¹ᵁ ((L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull V.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr _ _ h0, map_mul, ← ProjSpace.fnOf_appLE g hgη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L.B V.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.B.pull b) V'.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hj _ _ _ _ _
  · intro i x hx
    rw [hr', hφ, ← map_mul, ← hπx]
    exact unitAt_fnMap_of g hgη (hu _ _ (hch i x hx))
  · intro σ z y y' i e1 e2 hi
    let z0 : CxPts (V.π ≫ Y.str) σ := ⟨z.1 ≫ g, by rw [Category.assoc, ← Category.assoc g, hπ]; exact z.2⟩
    let y0 := Points.PtsOver.map b hb _ y'
    have e1' : y.1 = z0.1 ≫ V.π := by
      rw [e1]
      show z.1 ≫ V'.π = (z.1 ≫ g) ≫ V.π
      rw [Category.assoc, hπ]
    have e2' : y0.1 = z0.1 ≫ V.j := by
      show y'.1 ≫ b = (z.1 ≫ g) ≫ V.j
      rw [e2, Category.assoc, hj, Category.assoc]
    have hi0 : under z0 ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := hch i _ hi
    have H := hc σ z0 y y0 (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi0
    have hπ0 : V.π (under z0) = under y := by
      show _ = y.1 _
      rw [e1']
      rfl
    have hU := hu _ _ hi0
    rw [hπ0] at hU
    have hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y0 :=
      (L.φ _).pull_φ b hb (i PUnit.unit) y'
    rw [H, hr', hφ, ← map_mul, hw, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of g hgη hU.regAt),
      SmallSec.ratVal_eq_valAt z0 hU.regAt, SmallSec.valAt_fnMap g hgη z.1 hU.regAt]
  · intro v e y z yt i e1 e2 hi
    have e1' : (z ≫ g) ≫ V.π = y.1 := by rw [Category.assoc, hπ, e1]
    have e2' : spMap e.O.subtype ≫ (yt ≫ b) = (z ≫ g) ≫ V.j := by
      rw [← Category.assoc, e2, Category.assoc, hj, Category.assoc]
    have hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hfin v e y (z ≫ g) (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e1' e2' hi'
    have hmem : below (z ≫ g) ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : ((z ≫ g) ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e2']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ0 : V.π (below (z ≫ g)) = below y.1 := by
      rw [← e1']
      rfl
    have hU := hu _ _ hmem
    rw [hπ0] at hU
    rw [H, hr', hφ, ← map_mul, SmallSec.valAt_fnMap g hgη z hU.regAt]

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsScaleByConstant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNormConst

open GlobalTheory.Cartier GlobalTheory.CxPts

theorem norms_const_mul : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : F), c ≠ 0 → Norms V L f a l →
    Norms V L f (fun σ y => a σ y + Real.log ‖σ c‖)
      (fun v e y => l v e y + Real.log (NumberField.HeightOneSpectrum.adicAbv F v c)) := by
  intro F _ _ Y V L f a l c hc ⟨r, hr, hu, hinf, hfin⟩
  have hcu (x : V.G) := IndScale.unitAt_constFn (V.π ≫ Y.str) x hc
  let cu : V.G.functionFieldˣ := Units.mk0 (Cartier.constFn (V.π ≫ Y.str) c) (hcu (genericPoint V.G)).ne_zero
  have hcv : (cu : V.G.functionField) = Cartier.constFn (V.π ≫ Y.str) c := rfl
  refine ⟨fun i => r i * cu, fun i j h => ?_, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · simp only [Units.val_mul]
    rw [hr i j h, mul_assoc]
  · rw [Units.val_mul, ← mul_assoc]
    exact (hu i x hx).mul (hcu x)
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu i _ hi
    rw [hπ] at hU
    beta_reduce
    rw [hinf σ z y y' i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      ratVal_mul hU.regAt (hcu _).regAt, IndScale.ratVal_constFn, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hU)) (norm_ne_zero_iff.2 ((map_ne_zero σ).2 hc))]
    ring
  · have hz : below z ∈ (L.B.pull V.j).U i := Set.mem_iInter.2 fun _ => by
      change (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ L.B.U (i PUnit.unit)
      rw [← e₂]
      exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial
    have hπ : V.π (below z) = below y.1 := by
      show _ = y.1 _
      rw [← e₁]
      rfl
    have hU := hu i _ hz
    rw [hπ] at hU
    have hy : z ≫ (V.π ≫ Y.str) = spMap (algebraMap F (AlgebraicClosure F)) := by
      rw [← Category.assoc, e₁]
      exact y.2
    beta_reduce
    rw [hfin v e y z yt i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      OfModel.valAt_mul _ hU.regAt (hcu _).regAt, IndScale.valAt_constFn _ _ z hy, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (IndScale.valAt_ne_zero _ hU)) (AbsoluteValue.ne_zero _ hc)]

end GlobalTheory.CoverNormConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_pow {X Z : Scheme.{0}} [IsIntegral Z] (B : LB X) (j : Z ⟶ X) (m : ℕ)
    {r : (B.pull j).ι → Z.functionFieldˣ} (hr : IsRatSec (B.pull j) r) :
    IsRatSec ((lbPow B m).pull j) fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m := by
  intro i i' h
  have l₀ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U fun _ => i' PUnit.unit PUnit.unit :=
    fun _ hx => ⟨InducedPow.mem_chart B j m hx.1, InducedPow.mem_chart B j m hx.2⟩
  have l₁ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      j ⁻¹ᵁ ((lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₂ : (lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit) ≤
      B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₃ : (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U (fun _ => i' PUnit.unit PUnit.unit) ≤
      j ⁻¹ᵁ (B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr _ _ (l₀ h), mul_pow,
    InducedPow.pull_g _ j i i' l₁, InducedPow.pow_g B m _ _ l₂, map_pow, map_pow,
    InducedPow.pull_g B j _ _ l₃, ← fnOf_resG l₀ h]
  congr 3
  have e : j.appLE _ _ l₃ ≫ Z.presheaf.map (homOfLE l₀).op =
      X.presheaf.map (homOfLE l₂).op ≫ j.appLE _ _ l₁ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom (B.g (i PUnit.unit PUnit.unit) (i' PUnit.unit PUnit.unit)).val) e

theorem norms_pow : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (m : ℕ), Norms V L f a l → Norms V (L.pow m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  rintro F _ _ Y V L f a l m ⟨r, hr, hu, hc, hf⟩
  have key : ∀ (g : Y.Fn) (i : ((lbPow L.B m).pull V.j).ι),
      V.φ (g ^ m) * ((r (fun _ => i PUnit.unit PUnit.unit) ^ m : V.G.functionFieldˣ) : V.G.functionField) =
        (V.φ g * (r (fun _ => i PUnit.unit PUnit.unit) : V.G.functionField)) ^ m := by
    intro g i
    rw [map_pow, Units.val_pow_eq_pow_val, mul_pow]
  refine ⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m, isRatSec_pull_pow L.B V.j m hr, ?_, ?_, ?_⟩
  · intro i x hx
    show UnitAt x (V.φ (f (V.π x) ^ m) * _)
    erw [key]
    exact InducedPow.unitAt_pow (hu _ x (InducedPow.mem_chart L.B V.j m hx)) m
  · intro σ z y y' i e₁ e₂ hi
    have hi' := InducedPow.mem_chart L.B V.j m hi
    have H := hc σ z y y' (fun _ => i PUnit.unit PUnit.unit) e₁ e₂ hi'
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu _ _ hi'
    rw [hπ] at hU
    have h₄ : ((L.pow m).φ _).φ (i PUnit.unit) y' = (m : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y' :=
      ((L.φ _).zpow_φ _ _ y').trans (by simp)
    show (m : ℝ) * a σ y = Real.log ‖ratVal (V.φ (f (under y) ^ m) * _) z‖ - _
    erw [key, InducedPow.ratVal_pow z hU, norm_pow, Real.log_pow, h₄, H]
    ring
  · intro v e y z yt i e₁ e₂ hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hf v e y z yt (fun _ => i PUnit.unit PUnit.unit) e₁ e₂ hi'
    have hmem : below z ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂]
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu _ _ hmem
    rw [hπ] at hU
    show (m : ℝ) * l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1) ^ m) * _)))
    erw [key, InducedPow.valAt_pow _ hU.regAt, map_pow, Real.log_pow, H]

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_tens {X Z : Scheme.{0}} [IsIntegral Z] (A B : LB X) (j : Z ⟶ X)
    {r : (A.pull j).ι → Z.functionFieldˣ} {s : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (A.pull j) r) (hs : IsRatSec (B.pull j) s) :
    IsRatSec ((CechPic.tens A B).pull j)
      fun i => r (fun _ => (i PUnit.unit).1) * s fun _ => (i PUnit.unit).2 := by
  have cA {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  intro i i' h
  have lA := inf_le_inf (cA (i := i)) (cA (i := i'))
  have lB := inf_le_inf (cB (i := i)) (cB (i := i'))
  rw [Units.val_mul, Units.val_mul, hr _ _ (lA h), hs _ _ (lB h), mul_mul_mul_comm,
    ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul,
    InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]
  congr 2
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1)
      fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val
  · refine (congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2)
      fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val

theorem norms_tens : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f₁ : Y.X → Y.Fn) (a₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₁ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (f₂ : Y.X → Y.Fn) (a₂ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₂ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L₁ f₁ a₁ l₁ → Norms V L₂ f₂ a₂ l₂ → Norms V (L₁.tens L₂) (fun x => f₁ x * f₂ x) (fun σ y => a₁ σ y + a₂ σ y) (fun v e y => l₁ v e y + l₂ v e y) := by
  intro F _ _ Y V L₁ L₂ f₁ a₁ l₁ f₂ a₂ l₂ h₁ h₂
  obtain ⟨r₁, hr₁, hu₁, hc₁, hv₁⟩ := h₁
  obtain ⟨r₂, hr₂, hu₂, hc₂, hv₂⟩ := h₂
  have cA {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₁.B.pull V.j).U fun _ => (i PUnit.unit).1 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₂.B.pull V.j).U fun _ => (i PUnit.unit).2 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  have split : ∀ (i : ((L₁.tens L₂).B.pull V.j).ι) (g₁ g₂ : Y.Fn),
      V.φ (g₁ * g₂) * (((r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2) : V.G.functionFieldˣ)) :
        V.G.functionField) =
      (V.φ g₁ * (r₁ (fun _ => (i PUnit.unit).1) : V.G.functionField)) *
        (V.φ g₂ * (r₂ (fun _ => (i PUnit.unit).2) : V.G.functionField)) := by
    intro i g₁ g₂
    rw [map_mul, Units.val_mul]
    ring
  refine ⟨fun i => r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2),
    isRatSec_pull_tens L₁.B L₂.B V.j hr₁ hr₂, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · rw [split]
    exact (hu₁ _ x (cA hx)).mul (hu₂ _ x (cB hx))
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have H₁ := hc₁ σ z y y' _ e₁ e₂ (cA hi)
    have H₂ := hc₂ σ z y y' _ e₁ e₂ (cB hi)
    have U₁ := hu₁ _ _ (cA hi)
    have U₂ := hu₂ _ _ (cB hi)
    rw [hπ] at U₁ U₂
    have n₁ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₁)
    have n₂ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₂)
    beta_reduce
    rw [split, ratVal_mul U₁.regAt U₂.regAt, norm_mul, Real.log_mul n₁ n₂, H₁, H₂]
    change _ = _ - ((L₁.φ _).φ (i PUnit.unit).1 y' + (L₂.φ _).φ (i PUnit.unit).2 y') / 2
    ring
  · have H₁ := hv₁ v e y z yt (fun _ => (i PUnit.unit).1) e₁ e₂ (fun x hx => (hi hx).1)
    have H₂ := hv₂ v e y z yt (fun _ => (i PUnit.unit).2) e₁ e₂ (fun x hx => (hi hx).2)
    have hmem : below z ∈ ((L₁.tens L₂).B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ (L₁.tens L₂).B.U (i PUnit.unit) := by
        rw [← e₂]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have U₁ := hu₁ _ _ (cA hmem)
    have U₂ := hu₂ _ _ (cB hmem)
    rw [hπ] at U₁ U₂
    rw [split, SmallSec.valAt_mul U₁.regAt U₂.regAt, map_mul,
      Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero U₂)).ne', ← H₁, ← H₂]

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem norms_mul_unit : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ)
    (c : Y.X → Y.Fn), (∀ x, UnitAt x (c x)) → Norms V L f a l →
    Norms V L (fun x => c x * f x) (fun σ y => Real.log ‖ratVal (c (under y)) y‖ + a σ y)
      (fun v e y => Real.log (e.w (valAt y.1 (c (below y.1)))) + l v e y) := by
  intro F _ _ Y V L f a l c hc h
  obtain ⟨r, hr, hu, hcx, hfin⟩ := h
  have split : ∀ (i : (L.B.pull V.j).ι) (g : Y.Fn) (h : Y.Fn),
      V.φ (g * h) * (r i : V.G.functionField) = V.φ g * (V.φ h * (r i : V.G.functionField)) := by
    intro i g h
    rw [map_mul, mul_assoc]
  refine ⟨r, hr, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_, fun v e y z yt i e₁ e₂ hi => ?_⟩
  · rw [split]
    exact (V.unitAt_φ (hc (V.π x))).mul (hu i x hx)
  · have H := hcx σ z y y' i e₁ e₂ hi
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu i _ hi
    rw [hπ] at hU
    have hC : UnitAt (V.π (under z)) (c (under y)) := by rw [hπ]; exact hc _
    have hCφ := V.unitAt_φ hC
    have n1 : ratVal (c (under y)) y ≠ 0 := by
      rw [← V.ratVal_φ z y e₁ (hc _).regAt]
      exact ratVal_ne_zero (y := z) hCφ
    have n2 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z ≠ 0 := ratVal_ne_zero (y := z) hU
    beta_reduce
    rw [split, ratVal_mul hCφ.regAt hU.regAt, V.ratVal_φ z y e₁ (hc _).regAt, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 n1) (norm_ne_zero_iff.2 n2), H]
    ring
  · have H := hfin v e y z yt i e₁ e₂ hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e₂]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu i _ hmem
    rw [hπ] at hU
    have hC : UnitAt (V.π (below z)) (c (below y.1)) := by rw [hπ]; exact hc _
    have hCφ := V.unitAt_φ hC
    have n1 : e.w (valAt y.1 (c (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hc _))
    have n2 : e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU)
    beta_reduce
    rw [split, SmallSec.valAt_mul hCφ.regAt hU.regAt, V.valAt_φ z hC.regAt, e₁, map_mul,
      Real.log_mul n1 n2, H]

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelBijectiveOfPowEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omegaLevel_bijective_of_pow_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (n : ℕ), N ≤ n → Function.Bijective (G.omegaLevel n) := by
  intro p R _ N hN G n hn
  refine ⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩
  rw [← sub_eq_zero]
  have h0 : (w - w').1 n = 0 := by
    simp only [omegaLevel_apply] at h
    change w.1 n - w'.1 n = 0
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := (G.omega_val_eq_zero_iff n (w - w')).1 h0
  rw [hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRow3

theorem oneFormMapRow_threeLevel_of_characterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O ph hn hC hE hFW hIo i hP hT
  obtain ⟨hcore, hoff, hused⟩ := GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation D G Pl0 I0 T0 A3 T.Q.c.F R F hC hE
  exact GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O ph hn hcore hoff hused hFW hIo i hP hT

end GlobalTheory.OneMapRow3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_statement_holds : RestrictSt := by
  first | exact @GlobalTheory.FlatModel.restrictSt | exact GlobalTheory.FlatModel.restrictSt | (intros; apply GlobalTheory.FlatModel.restrictSt <;> assumption)
end

