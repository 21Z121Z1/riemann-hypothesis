import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtField
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecQuot

open TopologicalSpace

variable {X : Scheme.{0}} {L : LB X}

abbrev ch1 (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

theorem mem_finOnePowerChartOpen_iff {j : Fin 1 → L.ι} {x : X} : x ∈ ch1 L j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem gm_secM_g {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z (ch1 L j ⊓ ch1 L j') ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) r z j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast]

abbrev M1 (L : LB X) (k : ℕ) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))

theorem germ_finOnePowerLineBundle_transition_eq_pow {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z ((M1 L k).U j ⊓ (M1 L k).U j') ((M1 L k).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := gm_secM_g k r z j j' hj hj'

theorem lineBundlePowChartOpen_le_finOnePowerChartOpen (J : PUnit → L.ι) : powChart L J ≤ ch1 L (fun _ => J PUnit.unit) :=
  fun _ h => mem_finOnePowerChartOpen_iff.2 (mem_powChart.1 h)

def toPow {k : ℕ} (s : SecM (𝟙 X) L k) : (lbPow L k).Sec :=
  powSecOfGerm k (fun J => resG X (lineBundlePowChartOpen_le_finOnePowerChartOpen J) (s.f fun _ => J PUnit.unit)) fun y J J' hJ hJ' => by
    have e := gs_compat s (𝟙 X) y (j := fun _ => J PUnit.unit) (j' := fun _ => J' PUnit.unit)
      (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    have e2 := germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    refine (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _).trans (e.trans ?_)
    refine (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J') hJ' _).symm).trans ?_
    rw [Units.val_pow_eq_pow_val]

theorem gs_toPow {k : ℕ} (s : SecM (𝟙 X) L k) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (J : PUnit → L.ι)
    (hJ : r z ∈ powChart L J) : gs r z _ (powFn (toPow s) J) = gs r z _ (s.f fun _ => J PUnit.unit) :=
  gs_res r z (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _

theorem exists_secM_of_pow {n N : ℕ} (hn : n = N) (u : (lbPow L n).Sec) :
    ∃ c : SecM (𝟙 X) L N, ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ ch1 L j →
      gs r z _ (c.f j) = gs r z _ (powFn u (fun _ => j 0)) := by
  subst hn
  have le : ∀ j : Fin 1 → L.ι, ch1 L j ≤ powChart L (fun _ => j 0) := fun j _ h => mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 h)
  refine ⟨GlobalTheory.LBGerm.secOfGerm (M := M1 L n) (fun j => resG X (le j) (powFn u (fun _ => j 0)))
    fun y (j j' : Fin 1 → L.ι) hj hj' => ?_, fun r z j hj => gs_res r z (le j) hj _⟩
  have e := gs_powFn_compat u (𝟙 X) y _ _ (le j hj) (le j' hj')
  have e2 := germ_finOnePowerLineBundle_transition_eq_pow n (𝟙 X) y j j' hj hj'
  refine (gs_res (𝟙 X) y (le j) hj _).trans (e.trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res (𝟙 X) y (le j') hj' _)).symm
  rw [Units.val_pow_eq_pow_val]

theorem gs_appLE₁ {Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y)
    (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr₁ {A : Type} [CommRing A] (x : Sp A ⟶ X) {U U' : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hU' : ⊤ ≤ x ⁻¹ᵁ U') (a : Γ(X, U)) (a' : Γ(X, U')) (h : ∀ z, gs x z U a = gs x z U' a') :
    valR x U a = valR x U' a' := by
  rw [valR, valR, dif_pos hU, dif_pos hU']
  refine congrArg _ (fn_ext fun z hz => ?_)
  rw [gs_appLE₁ _ _ _ _ _ _ hz, gs_appLE₁ _ _ _ _ _ _ hz]
  simp only [Category.id_comp]
  exact h z

theorem mem_of_top_le {A : Type} [CommRing A] {x : Sp A ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp A) :
    x z ∈ U := h (show z ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_mul_pow_of_gs {A : Type} [CommRing A] (x : Sp A ⟶ X) {U V W : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hW : ⊤ ≤ x ⁻¹ᵁ W) (c : Γ(X, U)) (f : Γ(X, V)) (s : Γ(X, W)) (m : ℕ)
    (h : ∀ z, gs x z U c = gs x z V f * gs x z W s ^ m) : valR x U c = valR x V f * valR x W s ^ m := by
  have hO : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) := fun z hz => ⟨hV hz, hW hz⟩
  have e1 : valR x V f = valR x (V ⊓ W) (resG X inf_le_left f) :=
    valR_congr₁ x hV hO _ _ fun z => (gs_res x z inf_le_left (mem_of_top_le hO z) f).symm
  have e2 : valR x W s = valR x (V ⊓ W) (resG X inf_le_right s) :=
    valR_congr₁ x hW hO _ _ fun z => (gs_res x z inf_le_right (mem_of_top_le hO z) s).symm
  have e3 : valR x U c = valR x (V ⊓ W) (resG X inf_le_left f * resG X inf_le_right s ^ m) :=
    valR_congr₁ x hU hO _ _ fun z => by
      rw [h z, gs_mul _ z _ (mem_of_top_le hO z), GlobalTheory.LBGerm.gs_pow _ z _ (mem_of_top_le hO z),
        gs_res x z inf_le_left (mem_of_top_le hO z), gs_res x z inf_le_right (mem_of_top_le hO z)]
  rw [e1, e2, e3, valR, valR, valR, dif_pos hO, dif_pos hO, dif_pos hO, map_mul, map_mul, map_pow, map_pow]

theorem nonzeroLocus_toPow {k : ℕ} (s : SecM (𝟙 X) L k) : nonzeroLocus (toPow s) = nonzeroLocus s := by
  refine nonzeroLocus_eq_of (toPow s) _ (fun y hy => ?_) fun y J hJ => ?_
  · have ⟨j, hj⟩ : ∃ j : Fin 1 → L.ι, y ∈ ch1 L j := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j 0, mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 hj)⟩
  · have e : gs (𝟙 X) y _ ((toPow s).f J) = gs (𝟙 X) y _ (s.f fun _ => J PUnit.unit) := gs_toPow s (𝟙 X) y J hJ
    rw [e]
    exact (mem_nonzeroLocus_iff_isUnit s (k := fun _ => J PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ)).symm

theorem extend_part [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {k : ℕ} (s : SecM (𝟙 X) L k)
    (f : Γ(X, nonzeroLocus s)) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N,
      ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i → r z ∈ nonzeroLocus s →
        gs r z _ (c.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  have hs' := nonzeroLocus_toPow s
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (toPow s) ⊓ powChart L J ≤ nonzeroLocus s :=
    fun J => inf_le_left.trans hs'.le
  obtain ⟨N₀, hN₀⟩ := exists_sec_eq_pow_mul (m := 0) hL (toPow s) (fun J => resG X (le J) f)
    (GlobalTheory.LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hy hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
      exact (gs_res (𝟙 X) y (le J) ⟨hy, hJ⟩ f).trans (gs_res (𝟙 X) y (le J') ⟨hy, hJ'⟩ f).symm)
  refine ⟨N₀, fun m N hm hN => ?_⟩
  obtain ⟨u, hu⟩ := hN₀ m hm
  obtain ⟨c, hc⟩ := exists_secM_of_pow (show 0 + k * m = N by omega) u
  refine ⟨c, fun r z i hi hz => ?_⟩
  have hJ : r z ∈ powChart L (fun _ => i) := mem_powChart.2 hi
  have hy : r z ∈ nonzeroLocus (toPow s) ⊓ powChart L (fun _ => i) := ⟨by rw [hs']; exact hz, hJ⟩
  have e := congrArg (gs r z _) (hu (fun _ => i))
  rw [gs_res r z _ hy, gs_mul r z _ hy, GlobalTheory.LBGerm.gs_pow r z _ hy, gs_res r z _ hy, gs_res r z _ hy] at e
  rw [hc r z (fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi), e, gs_toPow s r z _ hJ, _root_.mul_comm]

theorem quot_part {k : ℕ} (s : SecM (𝟙 X) L k) (m N : ℕ) (hN : N = k * m) (ρ : SecM (𝟙 X) L N) :
    ∃ f : Γ(X, nonzeroLocus s), ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i →
      r z ∈ nonzeroLocus s →
      gs r z _ (ρ.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  subst hN
  have loc : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X, X.basicOpen (s.f j)),
      resG X (X.basicOpen_le _) (ρ.f j) = a * resG X (X.basicOpen_le _) (s.f j) ^ m := fun j => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG X (X.basicOpen_le (s.f j)) (s.f j)) from
      X.toRingedSpace.isUnit_res_basicOpen (s.f j)).exists_left_inv
    refine ⟨resG X (X.basicOpen_le _) (ρ.f j) * b ^ m, ?_⟩
    have key : ∀ {R : Type} [CommRing R] (x y c : R), c * y = 1 → x = x * c ^ m * y ^ m := fun x y c h => by
      rw [_root_.mul_assoc, ← _root_.mul_pow, h, _root_.one_pow, _root_.mul_one]
    exact key _ _ _ hb
  choose a ha using loc
  have hga : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ X.basicOpen (s.f j) →
      gs r z _ (ρ.f j) = gs r z _ (a j) * gs r z _ (s.f j) ^ m := fun r z j hz => by
    have e := congrArg (gs r z _) (ha j)
    have e1 := gs_res r z (X.basicOpen_le (s.f j)) hz (ρ.f j)
    have e2 := gs_res r z (X.basicOpen_le (s.f j)) hz (s.f j)
    have e3 := gs_mul r z _ hz (a j) (resG X (X.basicOpen_le (s.f j)) (s.f j) ^ m)
    have e4 := GlobalTheory.LBGerm.gs_pow r z _ hz (resG X (X.basicOpen_le (s.f j)) (s.f j)) m
    exact e1.symm.trans (e.trans (e3.trans (congrArg _ (e4.trans (congrArg (· ^ m) e2)))))
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (s.f j)) (nonzeroLocus s)
    (fun j => homOfLE (GlobalTheory.basicOpen_le_nonzeroLocus s j)) le_rfl a (fun i j => fn_ext fun y hy => by
      have hi : y ∈ ch1 L i := X.basicOpen_le _ hy.1
      have hj : y ∈ ch1 L j := X.basicOpen_le _ hy.2
      refine (gs_res (𝟙 X) y inf_le_left hy (a i)).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy (a j)).symm)
      have u : IsUnit (gs (𝟙 X) y _ (s.f i) ^ m) :=
        ((GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y _ hi _).2 hy.1).pow m
      refine u.mul_right_cancel ?_
      rw [← hga (𝟙 X) y i hy.1, gs_compat ρ (𝟙 X) y hi hj, gs_compat s (𝟙 X) y hi hj, hga (𝟙 X) y j hy.2,
        germ_finOnePowerLineBundle_transition_eq_pow (k * m) (𝟙 X) y i j hi hj, germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y i j hi hj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val]
      ring)
  refine ⟨f, fun r z i hi hz => ?_⟩
  have hz' : r z ∈ X.basicOpen (s.f fun _ => i) := (mem_nonzeroLocus_iff_basicOpen s (k := fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi)).1 hz
  rw [hga r z _ hz', ← hf (fun _ => i)]
  exact congrArg (· * _) (gs_res r z (GlobalTheory.basicOpen_le_nonzeroLocus s _) hz' f)

theorem valR_secM_eq_mul_pow : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  intro X _ _ L hL F _ ξ j₀ hj₀ k s hs
  have hc : ⊤ ≤ ξ ⁻¹ᵁ ch1 L (fun _ => j₀) := fun z hz => mem_finOnePowerChartOpen_iff.2 (hj₀ hz)
  refine ⟨fun f => ?_, fun m N hN ρ => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := extend_part hL s f
    refine ⟨m₀, fun m N hm hN => ?_⟩
    obtain ⟨c, hc'⟩ := hm₀ m N hm hN
    exact ⟨c, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hc' ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩
  · obtain ⟨f, hf⟩ := quot_part s m N hN ρ
    exact ⟨f, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hf ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩

end GlobalTheory.SecQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultiple
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecScalVal

theorem val_of_secScal : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  intro X₂ Y L₂ f₂ k σ s c hs F _ ξ i hi
  have hc := hs (fun _ => i) (fun _ => i) (fun a b _ => by rcases a <;> rcases b <;> rfl)
  have hW : ⊤ ≤ ξ ⁻¹ᵁ (LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) (fun _ => i)) := by
    intro y _
    have hy := hi (Set.mem_univ y)
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · simpa using hy
    · simpa using hy
  have hv := congrArg (valR ξ _) hc
  rw [GlobalTheory.ZH.CrdCalc.valR_mul ξ _ hW] at hv
  erw [GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW, GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW,
    GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW] at hv
  have hσ : ⊤ ≤ ξ ⁻¹ᵁ f₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) :=
    hW.trans (ξ.preimage_mono (inf_le_right.trans
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)))
  have hσ' : ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) := hσ
  rw [GlobalTheory.ZH.CrdCalc.valR_eq ξ _ hσ] at hv
  exact (GlobalTheory.ZH.CrdCalc.valR_eq (ξ ≫ f₂) _ hσ' _).trans hv

end GlobalTheory.SecScalVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIso
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

noncomputable section
namespace GlobalTheory.GermVal

theorem valR_linComb_germ : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w k σ' s H F _ _ ξ i j h2 h1
  have m2 : f₂ (ξ (IsLocalRing.closedPoint F)) ∈ L₂.U i := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₂) _).1 h2
  have m1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ L₁.U j := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₁) _).1 h1
  have hy := H (ξ (IsLocalRing.closedPoint F)) i j m2 m1
  have a2 : ξ (IsLocalRing.closedPoint F) ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => m2
  have aw : ξ (IsLocalRing.closedPoint F) ∈
      ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => m2, Set.mem_iInter.2 fun _ => m1⟩
  have a1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ (LB.LinComb L₁ (K := Fin 1) (fun _ => 𝟙 X₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => m1
  rw [GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ a2, GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ aw,
    GlobalTheory.ZH.ThetaData.valR_eq_gs (ξ ≫ f₁) _ a1, gs_stalkMap ξ _ _ a2, gs_stalkMap ξ _ _ aw,
    gs_comp ξ f₁ _ _ a1, hy]
  simp only [map_mul, map_pow]

end GlobalTheory.GermVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValue
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem valR_of_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  intro X L hL Ω _ _ x g k σ ω hv i hi
  set z := IsLocalRing.closedPoint Ω
  have hxz : x z ∈ L.U i := hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hxz)
  have h := hv (Sp Ω) (𝟙 _) z J hJ
  have e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  have e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  rw [sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2),
    Category.id_comp] at h
  have m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have a1 : valR x _ (σ.f fun _ => i) =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i)) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _
  have mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i) := Set.mem_iInter.2 fun _ => hxz
  have a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _
  have a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val :=
    gs_unit _ _ _ mG _
  have hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω := by
    rw [← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]
    simp [GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]
  rw [a1, a2, a3]
  have h' := congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h
  rw [map_mul, hω, Units.val_pow_eq_pow_val, map_pow] at h'
  exact h'

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PrimDescent

theorem isPrim_of_unif : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  intro R _ _ _ I hI D A G _ _ hS U O _ _ _ o oA oG hlin w hprim
  have := hI.2.2.2
  haveI := oG.hom w
  haveI := oG.hom (1 + w)
  haveI := o.onB.hom w
  haveI := o.onB.hom (1 + w)
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hprim
  have hRig := GlobalTheory.PullGenG.hasGen_one U.LG
  have h0 := (HasGen.of_gen ρ hρ).neg.add hRig
  obtain ⟨uΨ, huΨ⟩ := h0.gen U.LG.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) (oG.act w)).left, 𝟙 G.left, (oG.act w).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised U.LG.isLB (oG.act w) uΨ huΨ
  have iG : ∀ i, IsMonHom ((![oG.act (1 + w), 𝟙 G, oG.act w, 1] : Fin 4 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [oG.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 G)), oG.hom w, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have iB : ∀ i, IsMonHom ((![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] : Fin 4 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) :=
    fun i => by
    fin_cases i
    exacts [o.onB.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 _)), o.onB.hom w,
      inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.UT.PullDescent.exists_descent U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_four]
      show c ^ (1 : ℤ) * c ^ (-2 : ℤ) * c ^ (-1 : ℤ) * c ^ (2 : ℤ) = 1
      group)
    ![oG.act (1 + w), 𝟙 G, oG.act w, 1] ![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · exact hlin.q_lin e (1 + w)
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact hlin.q_lin e w
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by
      fin_cases i
      · show (oG.act (1 + w)).left = (padd G (𝟙 _) (oG.act w)).left
        rw [oG.map_add, oG.map_one]
      all_goals rfl)
    (ψ := ![(padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left, 𝟙 D.toPre.P.A.left, (o.onB.act w).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left])
    (fun i => by
      fin_cases i
      · show (o.onB.act (1 + w)).left = (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left
        rw [o.onB.map_add, o.onB.map_one]
      all_goals rfl) u hu hn
  exact ⟨κ, hκ.1⟩

end GlobalTheory.PrimDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycle
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KappaCoc

theorem resG_resG' (Z : Scheme.{0}) {U V O : Z.Opens} (h : V ≤ U) (h' : O ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem dlog_cocycle {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (L : LB Z) (hL : L.IsLB) {a b c : L.ι} {W₁ W₂ W₃ : Z.Opens} (h₁ : W₁ ≤ L.U a) (h₂ : W₂ ≤ L.U b)
    (h₃ : W₃ ≤ L.U c) (hW₁ : W₁ ≤ W₀) (hW₂ : W₂ ≤ W₀) :
    resG Z (inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂) (d (W₁ ⊓ W₂) (resG Z (inf_le_inf h₁ h₂) (L.g a b).val) *
        resG Z (inf_le_inf h₁ h₂) (L.g a b)⁻¹.val) +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃)
        (d (W₂ ⊓ W₃) (resG Z (inf_le_inf h₂ h₃) (L.g b c).val) * resG Z (inf_le_inf h₂ h₃) (L.g b c)⁻¹.val) =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃)
        (d (W₁ ⊓ W₃) (resG Z (inf_le_inf h₁ h₃) (L.g a c).val) * resG Z (inf_le_inf h₁ h₃) (L.g a c)⁻¹.val) := by
  have l₁ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂ := inf_le_left
  have l₂ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hV : W₁ ⊓ W₂ ⊓ W₃ ≤ W₀ := inf_le_left.trans (inf_le_left.trans hW₁)
  have lU : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U a ⊓ L.U b ⊓ L.U c := inf_le_inf (inf_le_inf h₁ h₂) h₃
  have comm : ∀ {O : Z.Opens} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ O), O ≤ W₀ → ∀ x : Γ(Z, O),
      resG Z h (d O x) = d _ (resG Z h x) := fun h hO x => (hd.2.2 _ _ h hO x).symm
  rw [map_mul, map_mul, map_mul, comm l₁ (inf_le_left.trans hW₁), comm l₂ (inf_le_left.trans hW₂),
    comm l₃ (inf_le_left.trans hW₁), resG_resG', resG_resG', resG_resG', resG_resG', resG_resG', resG_resG']
  have uv : ∀ {p q : L.ι} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U p ⊓ L.U q),
      resG Z h (L.g p q).val * resG Z h (L.g p q)⁻¹.val = 1 := fun h => by
    rw [← map_mul, Units.mul_inv, map_one]
  have co := congrArg (fun u : Γ(Z, L.U a ⊓ L.U b ⊓ L.U c)ˣ => resG Z lU u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at co
  change resG Z lU (resG Z _ (L.g a b).val) * resG Z lU (resG Z _ (L.g b c).val) =
    resG Z lU (resG Z _ (L.g a c).val) at co
  rw [resG_resG', resG_resG', resG_resG'] at co
  have e := hd.2.1 _ hV (resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val)
    (resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val)
  rw [co] at e
  have ua := uv (l₁.trans (inf_le_inf h₁ h₂))
  have ub := uv (l₂.trans (inf_le_inf h₂ h₃))
  have uc := uv (l₃.trans (inf_le_inf h₁ h₃))
  set A := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val
  set B := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val
  set C := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c).val
  set A' := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b)⁻¹.val
  set B' := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c)⁻¹.val
  set C' := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c)⁻¹.val
  set dA := d _ A
  set dB := d _ B
  set dC := d _ C
  linear_combination (-C') * e - (dA * A' * C' + dB * B' * C') * co + dA * B * C' * ua + dB * A * C' * ub -
    (dA * A' + dB * B') * uc

end GlobalTheory.KappaCoc

theorem GlobalTheory.KappaCoc.kappa_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  intro E _ _ _ H X t U n δ hδ J W j _ _ hWU hj b i i' i''
  exact GlobalTheory.KappaCoc.dlog_cocycle (hδ b) t.PP.L t.PP.isLB (hj i) (hj i') (hj i'') (hWU i) (hWU i')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackLineBundleAutomorphismEqConstStatement
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
theorem _root_.GlobalTheory.T.pulledBackLineBundle_automorphism_eq_const : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  first | exact @GlobalTheory.PullAutConst.main | exact GlobalTheory.PullAutConst.main | (intros; apply GlobalTheory.PullAutConst.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeightStatement
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
theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartFunctions_isWeight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  first | exact @GlobalTheory.Heat.TermWt.isWt_term | exact GlobalTheory.Heat.TermWt.isWt_term | (intros; apply GlobalTheory.Heat.TermWt.isWt_term <;> assumption)
end

