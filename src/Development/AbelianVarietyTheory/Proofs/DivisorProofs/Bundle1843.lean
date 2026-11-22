import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open Filter Topology

noncomputable section

namespace GlobalTheory.PureGlue

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_slice (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (z : κ → Af F) :
    ∃ f : SInf F κ, ∀ a : κ → AF F, (∀ i, (a i).2 = z i) → Φ a = f (fun i => evI F (a i)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, -, rfl⟩ := hΦ
    refine ⟨g z • f, fun a ha => ?_⟩
    have h : (fun i => (a i).2) = z := funext ha
    show f _ * g (fun i => (a i).2) = _
    rw [h, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    rfl
  | zero => exact ⟨0, fun a _ => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    exact ⟨f1 + f2, fun a ha => by simp [hf1 a ha, hf2 a ha]⟩
  | smul c Φ _ h =>
    obtain ⟨f1, hf1⟩ := h
    exact ⟨c • f1, fun a ha => by simp [hf1 a ha]⟩

theorem isLocallyConstant_fin (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (b : κ → Ainf F) :
    IsLocallyConstant (fun z : κ → Af F => Φ (fun i => (b i, z i))) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact (IsLocallyConstant.const (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (b i))).mul hg.1
  | zero => exact IsLocallyConstant.const 0
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.comp (fun t => c • t)

def hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) : Af F :=
  g + ∑ v ∈ S, singleFin v (evalV F v y - evalV F v g)

theorem evalV_hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (hyb S y g) = if u ∈ S then evalV F u y else evalV F u g := by
  unfold hyb
  rw [map_add, map_sum]
  split_ifs with hu
  · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
      evalV_singleFin_self]
    abel
  · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (by rintro rfl; exact hu hv) _), add_zero]

theorem hyb_insert {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (y g : Af F) :
    hyb (insert v S) y g = hyb S y g + singleFin v (evalV F v y - evalV F v g) := by
  unfold hyb
  rw [Finset.sum_insert hv]
  abel

theorem hyb_empty (y g : Af F) : hyb ∅ y g = g := by simp [hyb]

theorem tendsto_hyb (y g : Af F) : Tendsto (fun S => hyb S y g) atTop (𝓝 y) :=
  GlobalTheory.AdelicLimit.tendsto_finAdele _ y g
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_pos hv] at h; exact h)
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_neg hv] at h; exact h)

end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue
variable {F : Type} [Field F] [NumberField F]
theorem liftV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl
theorem liftV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).2 = singleFin v a := rfl
theorem fst_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).1 = p.1 := by
  change p.1 - (GlobalTheory.LatVac.liftV v a).1 + (GlobalTheory.LatVac.liftV v b).1 = p.1
  rw [liftV_fst, liftV_fst, sub_zero, add_zero]
theorem snd_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).2 = p.2 - singleFin v a + singleFin v b := by
  change p.2 - (GlobalTheory.LatVac.liftV v a).2 + (GlobalTheory.LatVac.liftV v b).2 = _
  rw [liftV_snd, liftV_snd]
end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue

open scoped Classical

theorem eq_pure_of_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  intro F _ _ κ _ vac hvac hcof Φ hΦ hsl
  set T0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1} with hT0
  have hT0f : T0.Finite := hcof
  have hex : ∀ v, ∃ ζ : κ → Fv F v, vac v ζ ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hvac v (funext h)
  let ζ : ∀ v, κ → Fv F v := fun v => if v ∈ T0 then (hex v).choose else 0
  have hζ1 : ∀ v, v ∉ T0 → vac v (ζ v) = 1 := by
    intro v hv
    have h : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := not_not.1 hv
    simp only [ζ, if_neg hv]
    rw [h, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun i => zero_mem _)]
    rfl
  have hζ : ∀ v, vac v (ζ v) ≠ 0 := by
    intro v
    by_cases hv : v ∈ T0
    · simp only [ζ, if_pos hv]
      exact (hex v).choose_spec
    · rw [hζ1 v hv]
      exact one_ne_zero
  let ξ0 : κ → Af F := fun i => ∑ v ∈ hT0f.toFinset, singleFin v (ζ v i)
  have hξ0 : ∀ v i, evalV F v (ξ0 i) = ζ v i := by
    intro v i
    simp only [ξ0, map_sum]
    by_cases hv : v ∈ T0
    · rw [Finset.sum_eq_single v (fun u _ hu => evalV_singleFin_ne (Ne.symm hu) _)
        (fun h => absurd (hT0f.mem_toFinset.2 hv) h), evalV_singleFin_self]
    · rw [Finset.sum_eq_zero (fun u hu => evalV_singleFin_ne
        (by rintro rfl; exact hv (hT0f.mem_toFinset.1 hu)) _)]
      simp [ζ, hv]
  set c : ℂ := ∏ v ∈ hT0f.toFinset, vac v (ζ v) with hcdef
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hζ v
  obtain ⟨f0, hf0⟩ := exists_slice Φ hΦ ξ0
  refine ⟨c⁻¹ • f0, ?_⟩
  funext x
  have hev : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : AF F), evFin F v a = evalV F v a.2 := fun _ _ => rfl
  let P : Finset (HeightOneSpectrum (𝓞 F)) → κ → AF F := fun S i => ((x i).1, hyb S (x i).2 (ξ0 i))
  have key : ∀ S, Φ (P S) * ∏ v ∈ S, vac v (ζ v) =
      Φ (P ∅) * ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
      let y : κ → AF F := fun k => P S k - GlobalTheory.LatVac.liftV v (ζ v k)
      have hy : ∀ k, evFin F v (y k) = 0 := by
        intro k
        simp only [y, map_sub, GlobalTheory.LatVac.evFin_liftV]
        rw [hev]
        change evalV F v (hyb S (x k).2 (ξ0 k)) - ζ v k = 0
        rw [evalV_hyb, if_neg hv, hξ0, sub_self]
      obtain ⟨a, ha⟩ := hsl v y hy
      have e1 : P S = y + fun k => GlobalTheory.LatVac.liftV v (ζ v k) := by
        funext k
        simp [y]
      have e2 : P (insert v S) = y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k)) := by
        funext k
        have hk : (y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))) k =
            P S k - GlobalTheory.LatVac.liftV v (ζ v k) + GlobalTheory.LatVac.liftV v (evFin F v (x k)) := rfl
        rw [hk]
        refine Prod.ext ?_ ?_
        · rw [fst_sub_add]
        · rw [snd_sub_add]
          show hyb (insert v S) (x k).2 (ξ0 k) =
            hyb S (x k).2 (ξ0 k) - singleFin v (ζ v k) + singleFin v (evFin F v (x k))
          rw [hyb_insert hv, hξ0, map_sub, hev]
          abel
      have h1 := ha (ζ v)
      have h2 := ha (fun i => evFin F v (x i))
      rw [← e1] at h1
      rw [← e2] at h2
      rw [Finset.prod_insert hv, Finset.prod_insert hv]
      linear_combination (vac v (ζ v) * ∏ u ∈ S, vac u (ζ u)) * h2 -
        (vac v (fun i => evFin F v (x i)) * ∏ u ∈ S, vac u (ζ u)) * h1 + vac v (fun i => evFin F v (x i)) * ih
  have hlc := isLocallyConstant_fin Φ hΦ (fun i => (x i).1)
  have ht : Tendsto (fun S => fun i => hyb S (x i).2 (ξ0 i)) atTop (𝓝 (fun i => (x i).2)) :=
    tendsto_pi_nhds.2 fun i => tendsto_hyb (x i).2 (ξ0 i)
  have hev1 : ∀ᶠ S in atTop, Φ (P S) = Φ x :=
    ht ((hlc.isOpen_fiber (Φ x)).mem_nhds rfl)
  have hxi : ∀ᶠ v in Filter.cofinite, ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (x i).2.2.mono fun v hv => hv
  set S0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F)} with hS0
  have hS0f : S0.Finite := hcof.and hxi
  have hev2 : ∀ᶠ S in atTop, hS0f.toFinset ∪ hT0f.toFinset ≤ S := Filter.eventually_ge_atTop _
  obtain ⟨S, hS1, hS2⟩ := (hev1.and hev2).exists
  have k := key S
  rw [hS1] at k
  have hcS : ∏ v ∈ S, vac v (ζ v) = c := by
    symm
    refine Finset.prod_subset (fun v hv => hS2 (Finset.mem_union_right _ hv)) ?_
    intro v _ hv
    exact hζ1 v (fun h => hv (hT0f.mem_toFinset.2 h))
  have hfp : ∏ᶠ v, vac v (fun i => evFin F v (x i)) = ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    apply hv
    show vac v (fun i => evFin F v (x i)) = 1
    have hn : v ∉ S0 := fun h => hvS (hS2 (Finset.mem_union_left _ (hS0f.mem_toFinset.2 h)))
    have h' := not_not.1 hn
    rw [h'.1, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h'.2)]
    rfl
  have hP0 : Φ (P ∅) = f0 (fun i => evI F (x i)) :=
    hf0 (P ∅) (fun i => by simp [P, hyb_empty])
  rw [hcS] at k
  show Φ x = (c⁻¹ • f0) (fun i => evI F (x i)) * ∏ᶠ v, vac v fun i => evFin F v (x i)
  rw [SchwartzMap.smul_apply, smul_eq_mul, hfp, ← hP0, mul_assoc, ← k, mul_comm (Φ x), ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.PureGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHilbertSamuelBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem geoBound_of_quoted' : Quoted → GeoBound := fun hQ =>
  GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound hQ (GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ hQ) (GlobalTheory.HeightTieProof.heightTie GlobalTheory.HSShort.htMul) GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

noncomputable def atW (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

theorem atW_apply (w : Pl D.host.E) (a : AE D) : atW w a = cpt w (toEAf D a) := rfl

theorem atW_atPl_self (w : Pl D.host.E) (x : Kw w) : atW w (atPl w x) = x := by
  classical
  rw [atW_apply, (atPl_spec w x).2 w, Pi.single_eq_same]

theorem atW_atPl_ne {w w' : Pl D.host.E} (h : w ≠ w') (x : Kw w') : atW w (atPl w' x) = 0 := by
  classical
  rw [atW_apply, (atPl_spec w' x).2 w, Pi.single_eq_of_ne h]

theorem atPl_one_mul (w : Pl D.host.E) (z : Kw w) : atPl w 1 * atPl w z = atPl w z := by
  classical
  refine ae_ext (by rw [map_mul, (atPl_spec w 1).1, zero_mul, (atPl_spec w z).1]) fun Q => ?_
  rw [map_mul, map_mul, (atPl_spec w 1).2 Q, (atPl_spec w z).2 Q]
  by_cases h : Q = w
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

namespace CoordinateMaps

variable (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
  (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)

theorem coord_add (y y' : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (y + y') = B.coord t w hX hY y + B.coord t w hX hY y' := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem coord_zero : B.coord t w hX hY 0 = 0 := by
  unfold Frames.coord
  rw [Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem coord_surj (z : Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w)) :
    ∃ y, B.coord t w hX hY y = z := by
  refine ⟨(loc w (B.β X.1 X.2)).val * (zᵀ.submatrix (Fin.cast (rank_vertex G t w hX).symm)
    (Fin.cast (rank_vertex G t w hY).symm)) * ((loc w (B.β Y.1 Y.2))⁻¹).val, ?_⟩
  unfold Frames.coord
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  ext a b
  simp only [transpose_apply, submatrix_apply, Fin.cast_cast, Fin.cast_eq_self]

end CoordinateMaps

end GlobalTheory.BigDat

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem map_atW_smul (w : Pl D.host.E) {m n : Type} (M : Matrix m n (AE D)) :
    (atPl w 1 • M).map (atW w) = M.map (atW w) := by
  refine Matrix.ext fun a b => ?_
  rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, atW_atPl_self, one_mul]

theorem mixCo_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : Pt G i j) :
    mixCo B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mapV e u).map (atW w)))
      (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((mapW e u).map (atW w)))ᵀ := rfl

theorem mixCo_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : Pt G i j, mixCo B t e w (u + x) = mixCo B t e w u + mixCo B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalf e (atPl w 1), mixCo B t e w x = z) ∧
    (∀ u : Pt G i j, mixCo B t e w (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = mixCo B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalf e (atPl w' 1), mixCo B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCo_eq, mixCo_eq, mixCo_eq, mapV_add, mapW_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      CoordinateMaps.coord_add, CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := CoordinateMaps.coord_surj B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomV G i j := y₁.map (atPl w)
    let x₂ : HomW G i j := y₂.map (atPl w)
    have k₁ : mapV e (ofMaps e (x₁, x₂)) = x₁ := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (x₁, x₂)) = x₂ := mapW_ofMaps e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapV e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapW e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCo_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapV e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapV e u := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapW e u := mapW_ofMaps e _
    rw [mixCo_eq, mixCo_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapV e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapV e x a b) = atW w (atPl w' 1 * mapV e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapW e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapW e x a b) = atW w (atPl w' 1 * mapW e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCo_eq, h₁, h₂, CoordinateMaps.coord_zero, CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end GlobalTheory.BigDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelW_forms_eq_principalForms : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → R.toRealDat.LUnif → R.PLevW F := by
  first | exact @GlobalTheory.LevW.levW_of_parts | exact GlobalTheory.LevW.levW_of_parts | (intros; apply GlobalTheory.LevW.levW_of_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelW_orthogonalSum_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).PartsW false := by
  first | exact @GlobalTheory.SumW.partsW_base | exact GlobalTheory.SumW.partsW_base | (intros; apply GlobalTheory.SumW.partsW_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinearFockPairingSqLeHermitianNormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  first | exact @GlobalTheory.FockCauchySchwarz.pairBK_sq_le | exact GlobalTheory.FockCauchySchwarz.pairBK_sq_le | (intros; apply GlobalTheory.FockCauchySchwarz.pairBK_sq_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBoundsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds : ∀ {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ (x : VV ℂ Λ),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (Formalism.L2.Col.Br.brStd hN Λ σ x) (Formalism.L2.Col.Br.brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) * (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  first | exact @GlobalTheory.BranchNormBound.brStd_norm_le | exact GlobalTheory.BranchNormBound.brStd_norm_le | (intros; apply GlobalTheory.BranchNormBound.brStd_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingMapExtendScalarsEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairF

theorem brPairF_map_descent : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1)
    (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) =
      GlobalTheory.BrPairF.brPairF σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ _ v) := by
  intro K ι _ _ _ φ n N hN Λ σ u v
  rw [← brPair_mapVV φ σ hN Λ u v, brPair, LinearMap.compl₁₂_apply, brPairF_apply, GlobalTheory.BrRat.covOf_eq]

end GlobalTheory.BrPairF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLatticeStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeSequence_first_map_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  first | exact @GlobalTheory.LattIota.iota_exists | exact GlobalTheory.LattIota.iota_exists | (intros; apply GlobalTheory.LattIota.iota_exists <;> assumption)
end

