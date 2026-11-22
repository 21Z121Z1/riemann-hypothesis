import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpLinComb

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverDominatingPair
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem exists_cover_dominating_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (W V : Mean4O.Cover Y)
    (k : W.G ⟶ V.G) (hk : k ≫ V.π = W.π) :
    ∃ (W' : Mean4O.Cover Y) (a : W'.X ⟶ W.X) (b : W'.X ⟶ V.X), a ≫ W.p = W'.p ∧ b ≫ V.p = W'.p ∧
      Lies W' W a ∧ Lies W' V b := by
  have H₀ := W.pb
  have := V.ar.isIntegral
  have := W.ar.isLocallyNoetherian
  have : IsProper W.p := CommonModel.isProper_of_isProjOver W.ar.isProjOver
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  let r := pullback.fst W.p V.p
  have hc : W.j ≫ W.p = (k ≫ V.j) ≫ V.p := by
    rw [W.pb.w, Category.assoc, Category.assoc, V.pb.w, ← hk]; simp only [Category.assoc]
  let h : W.G ⟶ pullback W.p V.p := pullback.lift W.j (k ≫ V.j) hc
  have hr : h ≫ r = W.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd W.p V.p = k ≫ V.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ W.p) := GlobalTheory.ProjSpace.isProjOver_pullback W.ar.isProjOver V.ar.isProjOver
  have w : h ≫ r ≫ W.p = (W.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))
  let f' : W.G ⟶ pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (W.π ≫ Y.str) w
  let ρ : pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) ⟶ W.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ W.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 W.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ W.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (W.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ W.p) F (W.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme W.G := isNormalScheme_G W
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have : IsPreimmersion W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = W.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd W.p V.p = k ≫ V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) W.j e₁
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← W.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ W.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ W.p) (W.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let W' : Mean4O.Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ r ≫ W.p
      ar := ⟨W.ar.isDomain, W.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := W.G
      j := h.toNormalization
      π := W.π
      pb := hpb'
      φ := W.φ
      φ_spec := W.φ_spec }
  refine ⟨W', h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd W.p V.p, Category.assoc _ _ _, ?_,
    ⟨𝟙 W.G, by rw [Category.id_comp]; exact e₁.symm, Category.id_comp _⟩, ⟨k, e₂.symm, hk⟩⟩
  change (h.fromNormalization ≫ pullback.snd W.p V.p) ≫ V.p = h.fromNormalization ≫ r ≫ W.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.Mean4O.CoverDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsPullbackPower
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

section Induces

open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem generatesAt_genAt_pow (D : Y.Dv) (k : ℕ) (x : Y.X) : (k • D).GeneratesAt x (genAt D x ^ k) := by
  have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn D x).nsmul k)
  rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this

theorem induces_twist_of_induced {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hA : A.Induced M L k cf) (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p)
    (hj : V.j ≫ b = V.π ≫ M.j) : V.Induces (A.twist 0 (-cf)) (L.pull b hb) k := by
  haveI := M.ar.isIntegral
  obtain ⟨-, r, hr, h₁, h₂⟩ := hA
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  set ψ := SmallSec.fnMap V.π hη with hψ
  have hφ : ∀ t, V.φ t = ψ t := fun t => by rw [e]
  have hg (x : Y.X) := generatesAt_genAt_pow A.D k x
  have hch : ∀ (i : ((L.pull b hb).B.pull V.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V.j).U i,
      V.π x ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L.B b V.j i hx) PUnit.unit
    have h2 : (V.j ≫ b) x = M.j (V.π x) := by rw [hj]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show M.j (V.π x) ∈ L.B.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull b hb).B.pull V.j).ι → V.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hmem : V.π (genericPoint V.G) ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) := ⟨hch i _ hij.1, hch j _ hij.2⟩
    have h0 : genericPoint Y.X ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) :=
      (genericPoint_specializes _).mem_open (TopologicalSpace.Opens.isOpen _) hmem
    have le : ((L.pull b hb).B.pull V.j).U i ⊓ ((L.pull b hb).B.pull V.j).U j ≤
        V.π ⁻¹ᵁ ((L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr.isRatSec _ _ h0, map_mul, ← ProjSpace.fnOf_appLE V.π hη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L.B M.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.B.pull b) V.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hj _ _ _ _ _
  · intro i x hx
    have hU := (hr.isEqn _ _ (hch i x hx)).generatesAt_iff.1 (hg (V.π x))
    rw [hr', hφ, ← map_pow, ← map_mul]
    exact unitAt_fnMap_of V.π hη hU
  · intro σ z y y' i e₁ e₂ hi
    change (Real.exp (-(2 * ((A.n : ℕ) : ℝ) * (A.ci (InfinitePlace.mk σ) + 0))) *
        C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ (k : ℕ) =
      ‖ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z‖ ^ 2 *
        Real.exp (-((L.pull b hb).φ _).φ (i PUnit.unit) y')
    let y₀ := Points.PtsOver.map b hb _ y'
    have e₂' : y₀.1 = y.1 ≫ M.j := by
      show y'.1 ≫ b = y.1 ≫ M.j
      rw [e₂, e₁, Category.assoc, hj, Category.assoc]
    have hπ₀ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hi₀ : under y ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := hπ₀ ▸ hch i _ hi
    have H := h₁ σ y y₀ (fun _ => i PUnit.unit PUnit.unit) _ e₂' hi₀ (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at H
    have hU := (hr.isEqn _ _ hi₀).generatesAt_iff.1 (hg (under y))
    have hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y₀ :=
      (L.φ _).pull_φ b hb (i PUnit.unit) y'
    have hv : ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z =
        ratVal (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) y := by
      have hU' : RegAt (V.π (under z)) (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
        rw [hπ₀]; exact hU.regAt
      rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of V.π hη hU'),
        SmallSec.ratVal_eq_valAt y hU.regAt, SmallSec.valAt_fnMap V.π hη z.1 hU', ← e₁]
    rw [hw, hv, ← H, add_zero, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  · intro v e y z yt i e₁ e₂ hi
    change ((k : ℕ) : ℝ) * (A.lg v e y - ((A.n : ℕ) : ℝ) * (-cf) v) =
      Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ (k : ℕ) * (r' i : V.G.functionField))))
    have e₂' : spMap e.O.subtype ≫ (yt ≫ b) = y.1 ≫ M.j := by
      rw [← Category.assoc, e₂, Category.assoc, hj, ← Category.assoc, e₁]
    have hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := h₂ v e y (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e₂' hi'
    have hmem : below y.1 ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hU := (hr.isEqn _ _ hmem).generatesAt_iff.1 (hg (below y.1))
    have hπ₀ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU' : RegAt (V.π (below z)) (genAt A.D (below y.1) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
      rw [hπ₀]; exact hU.regAt
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at H
    rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.valAt_fnMap V.π hη z hU', e₁, Pi.neg_apply]
    linarith [H]

end Induces

theorem norms_pull_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p), V.j ≫ b = V.π ≫ M.j → Norms V (L.pull b hb) (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => ((k : ℕ) : ℝ) * lnAdl A σ y) (fun v e y => ((k : ℕ) : ℝ) * A.lg v e y + ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * cf v) := by
  intro F _ _ C Y A M L k cf hA V b hb hj
  refine (norms_of_induces (induces_twist_of_induced hA V b hb hj)).congr (fun _ => rfl) (fun σ y => ?_) fun v e y => ?_
  · simp only [lnAdl, Adl.twist, Pi.add_apply, Pi.zero_apply, add_zero]
  · simp only [Adl.twist, Pi.neg_apply]
    ring

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechKS

theorem Pt.nonempty_affHom_of_in {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s) (h : P.In U.1) :
    Nonempty ((Pt.aff s U).Hom P) := by
  let φ := GlobalTheory.Points.valMap P.x U.1 h
  have hc : ∀ r : R, φ.hom (algebraMap R (CechDR.Sec s U.1) r) = algebraMap R P.B r := by
    intro r
    change φ.hom ((s.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [← GlobalTheory.Points.valR_eq P.x U.1 h, GlobalTheory.Points.valR_appLE P.x s le_top h, P.w,
      GlobalTheory.Points.valR_specMap]
    rfl
  refine ⟨⟨{ φ.hom with commutes' := hc }, ?_⟩⟩
  exact GlobalTheory.Points.specMap_valMap_fromSpec U.2 P.x h

theorem Pt.affHom_ρ_eq_valR {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a : (Pt.aff s U).Hom P) (b : Γ(X, U.1)) : a.ρ b = valR P.x U.1 b := by
  have hpre : ⊤ ≤ (CechDR.affPt s U) ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have hid : valR (CechDR.affPt s U) U.1 b = b := by
    rw [GlobalTheory.Points.valR_eq _ _ hpre]
    have h1 : Spec.map (𝟙 Γ(X, U.1)) ≫ U.2.fromSpec = CechDR.affPt s U := by
      rw [Spec.map_id, Category.id_comp]; rfl
    have h2 := GlobalTheory.Points.valMap_specMap_fromSpec U.2 (𝟙 Γ(X, U.1)) (h1 ▸ hpre)
    have h3 : GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre = 𝟙 _ := by
      have key : ∀ (x : Spec Γ(X, U.1) ⟶ X) (hx : x = CechDR.affPt s U) (h : ⊤ ≤ x ⁻¹ᵁ U.1),
          GlobalTheory.Points.valMap x U.1 h = GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre := by
        rintro _ rfl _; rfl
      exact (key _ h1 _).symm.trans h2
    rw [h3]; rfl
  rw [← a.pt, GlobalTheory.Points.valR_spMap_comp _ _ _ hpre, hid]
  rfl

theorem eq_of_valR_eq_on_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type} (W : J → X.Opens)
    (hW : ⨆ j, W j = ⊤) (V : X.Opens) (f g : Γ(X, V))
    (h : ∀ (P : Pt s) (j : J), P.In V → P.In (W j) → valR P.x V f = valR P.x V g) : f = g := by
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun x hx ↦ ?_
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxW
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W j) ⟨hx, hj⟩
  have hle : U' ≤ V ⊓ W j := hsub
  have hleV : U' ≤ V := hle.trans inf_le_left
  let Ua : X.affineOpens := ⟨U', hU'⟩
  have hPU : (Pt.aff s Ua).In U' := hU'.fromSpec_preimage_self.ge
  have hv := h (Pt.aff s Ua) j (hPU.mono hleV) (hPU.mono (hle.trans inf_le_right))
  have key : ∀ b : Γ(X, V), valR (Pt.aff s Ua).x V b = (X.presheaf.map (homOfLE hleV).op).hom b := by
    intro b
    rw [← GlobalTheory.Points.valR_res (Pt.aff s Ua).x hleV hPU b]
    exact (Pt.affHom_ρ_eq_valR s Ua (Pt.aff s Ua) (Pt.Hom.id _) _).symm
  rw [key, key] at hv
  have := congrArg (X.presheaf.germ U' x hxU') hv
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this

theorem Pt.affHom_subsingleton {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a a' : (Pt.aff s U).Hom P) : a = a' := by
  obtain ⟨ρ, e⟩ := a
  obtain ⟨ρ', e'⟩ := a'
  have : ρ = ρ' := AlgHom.ext fun b ↦ (Pt.affHom_ρ_eq_valR s U P ⟨ρ, e⟩ b).trans (Pt.affHom_ρ_eq_valR s U P ⟨ρ', e'⟩ b).symm
  subst this; rfl

theorem Pt.Hom.comp_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {P Q T : Pt s}
    (φ : P.Hom Q) (ψ : Q.Hom T) : (φ.comp ψ).triv = φ.triv ≫ ψ.triv :=
  Thick.hom_ext fun _ ↦ rfl

theorem h1_mk_mem_f1_of_isRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  intro R _ X s J W hW c hc
  obtain ⟨G, hG1, hG2⟩ := hc
  have hG : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P = G j' P := fun j j' P h h' ↦
    sub_eq_zero.1 (hG2 j j' P h h')
  change toH1O s (H1.mk _ c) = 0
  apply GlobalTheory.CechDR.cmpO_injective R X s
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine H1.mk_eq_zero.2 ?_
  classical
  let aP : ∀ (U : X.affineOpens) (P : Pt s), P.In U.1 → (Pt.aff s U).Hom P :=
    fun U P h ↦ (Pt.nonempty_affHom_of_in s U P h).some
  let FU : X.affineOpens → PtFn s := fun U P ↦
    if h : P.In U.1 ∧ ∃ j, P.In (W j) then G h.2.choose P - ev c (aP U P h.1).triv else 0
  have FU_eq : ∀ U (P : Pt s) j (hU : P.In U.1), P.In (W j) → FU U P = G j P - ev c (aP U P hU).triv := by
    intro U P j hU hj
    have h : P.In U.1 ∧ ∃ j, P.In (W j) := ⟨hU, j, hj⟩
    simp only [FU, dif_pos h]
    rw [hG _ j P h.2.choose_spec hj]
  have ex : ∀ U : X.affineOpens, ∃ f : Γ(X, U.1), ∀ (j : J) (P : Pt s), P.In (U.1 ⊓ W j) →
      FU U P = valR P.x U.1 f := by
    intro U
    refine GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R X s J (fun j ↦ U.1 ⊓ W j) U.1 (fun j ↦ inf_le_left) ?_ (FU U) ?_
    · rw [← inf_iSup_eq, hW, inf_top_eq]
    · intro j P Q φ hP
      have hU : P.In U.1 := hP.mono inf_le_left
      have hj : P.In (W j) := hP.mono inf_le_right
      rw [FU_eq U P j hU hj, FU_eq U Q j (hU.map φ) (hj.map φ),
        Pt.affHom_subsingleton s U Q (aP U Q (hU.map φ)) ((aP U P hU).comp φ), Pt.Hom.comp_triv, ev_comp,
        hG1 j P Q φ hj, map_sub]
      have e : φ.triv.φ (ev c (aP U P hU).triv) = φ.ρ (ev c (aP U P hU).triv) := rfl
      rw [e]; ring
  choose f hf using ex
  refine ⟨fun U ↦ f U.unop, ?_⟩
  funext U V a
  have hle : V.unop.1 ≤ U.unop.1 := leOfHom a.unop
  refine eq_of_valR_eq_on_cover s W hW V.unop.1 _ _ fun P j hV hj ↦ ?_
  change valR P.x V.unop.1 (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
    (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) = valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv)
  have hU : P.In U.unop.1 := hV.mono hle
  set b := aP V.unop P hV
  have e1 : valR P.x V.unop.1 (f V.unop) = FU V.unop P := (hf V.unop j P (hV.inf hj)).symm
  have e2 : valR P.x V.unop.1 (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) = FU U.unop P :=
    (GlobalTheory.Points.valR_res P.x hle hV (f U.unop)).trans (hf U.unop j P (hU.inf hj)).symm
  have e3 : aP U.unop P hU = (Pt.affHom s hle).comp b := Pt.affHom_subsingleton s _ P _ _
  have e4 : ev c (aP U.unop P hU).triv = b.ρ (ev c (Pt.affHom s hle).triv) + ev c b.triv := by
    rw [e3, Pt.Hom.comp_triv, ev_comp]; rfl
  have e5 : valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv) = b.ρ (ev c (Pt.affHom s hle).triv) :=
    (Pt.affHom_ρ_eq_valR s V.unop P b _).symm
  have e6 : b.ρ (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
      (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) =
      b.ρ (f V.unop) - b.ρ (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) := map_sub b.ρ _ _
  rw [e5, ← Pt.affHom_ρ_eq_valR s V.unop P b, e6, Pt.affHom_ρ_eq_valR s V.unop P b (f V.unop),
    Pt.affHom_ρ_eq_valR s V.unop P b (GlobalTheory.CechDR.Sec.res s hle (f U.unop)), e1, e2,
    FU_eq V.unop P j hV hj, FU_eq U.unop P j hU hj, e4]
  ring

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefectStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_secondSystem_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  first | exact @GlobalTheory.LiftSys.r_eq_neg_defect | exact GlobalTheory.LiftSys.r_eq_neg_defect | (intros; apply GlobalTheory.LiftSys.r_eq_neg_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧ (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D), fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧ (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)), ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  first | exact @GlobalTheory.PtExt.fv_linear | exact GlobalTheory.PtExt.fv_linear | (intros; apply GlobalTheory.PtExt.fv_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackChStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ q) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = bcPull w (fv f) := by
  first | exact @GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase | exact GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase | (intros; apply GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  first | exact @GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull | exact GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull | (intros; apply GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_translate_iso_cubical : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L → ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  first | exact @GlobalTheory.Mum.lam_transl_iso | exact GlobalTheory.Mum.lam_transl_iso | (intros; apply GlobalTheory.Mum.lam_transl_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  first | exact @GlobalTheory.CubeSymDescent.of_push | exact GlobalTheory.CubeSymDescent.of_push | (intros; apply GlobalTheory.CubeSymDescent.of_push <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8Power
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowE8

theorem exists_cp_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  intro S G₀ _ _ P W
  haveI hm : ∀ k : (Fin 8 × Fin 8) × Fin 4,
      IsMonHom ((![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
        Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2) := by
    rintro ⟨⟨a, b⟩, i⟩
    fin_cases i <;> dsimp <;>
      first
        | infer_instance
        | exact (inferInstance : IsMonHom (lift (powPr G₀ a) (powPr G₀ b) ≫ μ))
        | exact (inferInstance : IsMonHom (toUnit (powObj G₀ 8) ≫ η[G₀]))
  obtain ⟨Q, hQ⟩ := GlobalTheory.LinCombCP.exists_cp_linComb P (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => (![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
      Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  refine ⟨Q, hQ.trans ?_⟩
  unfold GlobalTheory.PowE8.e8LB GlobalTheory.LinCombCP.cpLB
  congr 1
  funext k
  rcases k with ⟨⟨a, b⟩, i⟩
  fin_cases i <;> rfl

end GlobalTheory.PowE8
end

