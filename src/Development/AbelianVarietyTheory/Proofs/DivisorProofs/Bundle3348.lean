import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3340

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianMetricGrading
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.SwapBundle

theorem swapFl_bundle : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp k) (d₁ : ℕ) (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) (E₁ : Y₁.Modules) (h₁ : VMetric q₁ E₁ 2)
      (H₁ : h₁.IsCInf) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (M : (Σ a, Fin (r a)) → HermLB q₁),
      D = d₁ + 1 ∧ IsArithVar q₁ d₁ ∧ IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i ((H a).pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i' ((H a).pull π w)) ∧
      ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        ((M z).pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := by
  intro k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl a i i' hi
  obtain ⟨Y₁, σ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, hY₁, hproj, hsurj, hdim, hfb, hS, hs, hj,
    hSv, hPv, hEv, hPj, hSj, hx, hz⟩ := GlobalTheory.T.flag_bundle_successive_quotient_line k B Y q p d D hq hp π w ι E r (fun a => (h a).isVB) fl hfl a i i' hi
  have wρ : ρ ≫ (σ ≫ q) = p := by rw [← Category.assoc, wσ, w]
  obtain ⟨d₁, hD, had⟩ := GlobalTheory.T.arith_variety_relative_dim_drop k Y Y₁ p (σ ≫ q) ρ D wρ hp hY₁ hproj hsurj hdim
  obtain ⟨h₁, H₁, i1, i2⟩ := GlobalTheory.T.metric_flag_successive_quotient_exact k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E a) (r a) (h a) (H a) (fl a) i i' hi
    S P E₁ s j t wst fl₁ hS hs hj hSv hPv hEv hPj hSj hx
  have key : ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ → ∃ M : HermLB (σ ≫ q),
      (M.pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := fun z hz' => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz z hz'.1 hz'.2
    exact GlobalTheory.T.metric_flag_quotient_connecting_map k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E z.1) (r z.1) (h z.1) (H z.1) (fl z.1) z.2 (A₀ z) (A₁ z)
      (u z) (v z) h1 h2 h3 h4 h5 h6
  refine ⟨Y₁, σ ≫ q, d₁, ρ, wρ, E₁, h₁, H₁, fl₁,
    fun z => if hz' : z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ then (key z hz').choose else HermLB.triv _,
    hD, had, hfb, i1, i2, fun z h1 h2 => ?_⟩
  simp only [dif_pos (show z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ from ⟨h1, h2⟩)]
  exact (key z ⟨h1, h2⟩).choose_spec

end GlobalTheory.SwapBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  first | exact @GlobalTheory.HTObjExt.extends_obj | exact GlobalTheory.HTObjExt.extends_obj | (intros; apply GlobalTheory.HTObjExt.extends_obj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLevelOfFixed
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isCompU_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {w : Pl E} {σ σ' : SmIrr (UL n w)}
    (h : IsCompU π w σ) (e : σ.ρ.Equiv σ'.ρ) : IsCompU π w σ' := by
  obtain ⟨p, hp, -, f, hf0, hfπ, hfe⟩ := h
  let g : σ'.V →ₗ[ℂ] σ.V := e.symm.toLinearEquiv.toLinearMap
  have hg : ∀ x v, g (σ'.ρ x v) = σ.ρ x (g v) := fun x v =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) v
  refine ⟨p, hp, σ'.irred, f ∘ₗ g, ?_, fun v => hfπ _, fun x v => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (e.toLinearEquiv v)
    simpa [g] using this
  · simp only [LinearMap.comp_apply, hg, hfe]

theorem hasLevel_of_fixed {S : Set (Pl E)} (hS : IsSection S) {π : Submodule ℂ (UA E n → ℂ)}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (h : π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) : HasLevel S π K' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨φ, (Submodule.mem_inf.1 hφ).1, hφ0, fun w hw x hx hk => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hk
  have hxf : x ∈ finU E n := hx.1
  have hmem : (⟨x, hxf⟩ : finU E n) ∈ globLev S K' := by
    simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map]
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      exact ⟨k, hk, hkx⟩
    · have hu : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        intro he
        exact hww ((hS w).unique ⟨hw', he⟩ ⟨hw, rfl⟩)
      have hker : x ∈ (cLoc w').ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 w') hu
      refine ⟨1, one_mem _, ?_⟩
      simpa using (MonoidHom.mem_ker.1 hker).symm
  have := (Submodule.mem_inf.1 hφ).2 ⟨_, hmem⟩
  simpa [fixed, eig, RF] using this

theorem dimW_ne_zero (lam : InfinitePlace E → DomWeight n) : dimW lam ≠ 0 := by
  unfold dimW
  rw [Finset.prod_ne_zero_iff]
  intro v _
  rw [map_one, LinearMap.trace_one]
  exact_mod_cast Module.finrank_pos.ne'

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isNef_pull : GlobalTheory.Published.ArCalc → SemiPull → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.IsNef D → (L.pull π hπ).IsNef E := by
  intro hA hS k _ X Y _ _ p q D E hX hY π hπ L hN
  obtain ⟨h, hh⟩ := ((hA.arExists k X p D hX).1 L)
  obtain ⟨h', hh'⟩ := ((hA.arExists k Y q E hY).1 (L.pull π hπ))
  have hL := (hh.isNef_iff hX).1 hN
  refine (hh'.isNef_iff hY).2 ⟨hS k X Y p q D E hX hY π hπ L hN.semiPos, fun Z i _ _ hd => ?_⟩
  rw [GlobalTheory.MixHt.heightProj k X Y p q D E hX hY π hπ L h h' hh hh' (i (genericPoint Z))]
  by_cases h0 : π.residueDegree (i (genericPoint Z)) = 0
  · simp [h0]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have hAY := GlobalTheory.MixHt.isAmb_of_isArithVar hY
  have hAX := GlobalTheory.MixHt.isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k Y q hAY
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.MixHt.hasDim_basic k X p hAX
  have hy : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) 1 := (hcl Z i _ 1).2 ((hgd Z 1).2 (by exact_mod_cast hd))
  obtain ⟨d', -, hd'⟩ := hm' (π (i (genericPoint Z)))
  obtain ⟨-, hiff⟩ := GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ _ 1 d' hy hd'
  have e1 : 1 = d' := hiff.1 h0
  subst e1
  obtain ⟨W, j, _, _, hj⟩ := exists_isClosedImmersion_genericPoint (π (i (genericPoint Z)))
  have hW : topologicalKrullDim W = (1 : ℕ) := (hgd' W 1).1 ((hcl' W j _ 1).1 (hj ▸ hd'))
  have := hL.2 W j (by exact_mod_cast hW)
  rwa [hj] at this

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealOrdersOfProperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.ideal_orders_of_proper_model : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a}) → (∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β) → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ
  haveI := hprop

  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  ·
    obtain ⟨K', _, σ, yK, hσ, hy⟩ := GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)
    obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ := GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ
    have hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a) := hτ
    obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by
      rw [Category.assoc, hy, spMap_comp, Category.assoc])
    have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
    obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
      GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)
    haveI := hfl
    haveI := hf₂l
    have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
        (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
        jK S ≫ spMap u = spMap uK ≫ jK R := by
      intro R S _ _ _ _ u uK hu
      change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

    have hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i := by
      have e1 := hjK f₂ fK₂ hf₂K
      calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
            simp only [Category.assoc]
        _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]
        _ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]
    obtain ⟨a', ha', hid⟩ := hord T₂ (spMap f₂ ≫ ξ') hcomm
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
      GlobalTheory.TraitOrder.idlAlong_comp] at hid

    set h := f₂.comp f with hh
    have hinj : Function.Injective h := hf₂i.comp hfi
    have hloc : IsLocalHom h := inferInstance
    have hne : h T.ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 T.irr.ne_zero
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit
      · exact hpos
    obtain ⟨b, hb, hI⟩ := GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid

    have hB₂ : GlobalTheory.Mum.Base T₂.V := ⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩
    obtain ⟨eq, heq⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _)
      hB₂ inferInstance hinj Function.injective_id hloc inferInstance
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl)
      (by
        rw [hT₂y, spMap_comp, Category.assoc]
        have hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
          simp [spMap]
        rw [hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)
    have hval : φ.evalZ T₂.β = e * φ.evalZ T.β := by
      rw [← hφ T e he1]
      unfold InvFun.evalZ
      rw [← φ.eval_equiv eq.toIntLinearEquiv]
      congr 1
      ext a c
      have := heq a c
      simp only [Nat.cast_one, one_mul] at this
      simp [AddEquiv.coe_toIntLinearEquiv, ← this]
    refine ⟨b, ?_, hI⟩
    have h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β) := by
      rw [← Nat.cast_mul, hb, ha', hval]; ring
    have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    exact mul_left_cancel₀ h2 h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTail
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlag
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem evalF_rename_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : Type}
    (u : α → A.Pt → Ev n) (v : β → A.Pt → Ev n) (R : MvPolynomial α ℝ) (Q : MvPolynomial β ℝ) :
    evalF A (Sum.elim u v) (rename Sum.inl R * rename Sum.inr Q) = evalF A u R * evalF A v Q := by
  funext x
  simp only [evalF, LineForm.fld, Pi.mul_apply, Polynomial.map_mul, MvPolynomial.map_rename, map_mul, aeval_rename]
  rfl

theorem evalF_chernRoots {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (m : ι → ℕ)
    (c : ι × ℕ → A.Pt → Ev n) (g : Root m → A.Pt → Ev n)
    (h : ∀ τ j p, c (τ, j) p = aeval (fun i => g ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j))
    (R : MvPolynomial (ι × ℕ) ℝ) : evalF A c R = evalF A g (chernRoots m R) := by
  funext p
  simp only [evalF, LineForm.fld]
  congr 1
  rw [aeval_map_algebraMap, aeval_map_algebraMap, chernRoots, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext x
  rw [h x.1 x.2 p, aeval_rename, aeval_esymm_eq_multiset_esymm, aeval_esymm_eq_multiset_esymm]
  rfl

theorem integral_chernF_mul_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  intro F _ σ X ι _ m E H hH R Q
  let ld : ι × ℕ → (atlas X σ).Pt → Ev X.dim := fun x => chernFld (atlas X σ) (fun y z => ldPart (gramAt E H x.1 y z)) x.2
  have hc : ∀ i, DbarCoh (atlas X σ) (Sum.elim (chernF E H) (grF E H) i) (Sum.elim ld (grF E H) i) := by
    rintro (⟨τ, j⟩ | x)
    · exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor F σ X ι m E H hH τ) j
    · exact GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ X ι m E H hH x
  have key := GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous (CxPts X.str σ) X.dim (atlas X σ) _ _ _ hc (rename Sum.inl R * rename Sum.inr Q)
  rw [evalF_rename_mul, evalF_rename_mul] at key
  rw [key, evalF_chernRoots (atlas X σ) m ld (grF E H) (fun τ j p => GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded F σ X ι m E H hH τ j p) R]
  simp only [evalF, LineForm.fld, map_mul]
  rfl

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.IsogTate

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

theorem vmap_comp' {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    vmap l (f ≫ g) = vmap l g ∘ₗ vmap l f := by
  simp only [vmap, tmap_comp, LinearMap.baseChange_comp]

theorem vmap_nsmul_id (A : AbVar K) (n : ℕ) (x : Vl l A) :
    vmap l (n • 𝟙 A) x = (n : ℚ_[l]) • x := by
  have h1 : tmap l A A (n • 𝟙 A) = (n : ℤ_[l]) • LinearMap.id := by
    rw [map_nsmul, tmap_id, Nat.cast_smul_eq_nsmul]
  rw [vmap, h1, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tmap_injective_of_finite_ker {A B : AbVar K} (f : A ⟶ B) (hG : Finite (ptMap f).ker) :
    Function.Injective (tmap l A B f) := by
  have hp : l.Prime := Fact.out
  set N := Nat.card (ptMap f).ker with hN
  have hN0 : 0 < N := Nat.card_pos
  have hx : ∀ x ∈ (ptMap f).ker, x ^ N = 1 := fun x hx => by
    have := pow_card_eq_one' (G := (ptMap f).ker) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  refine (injective_iff_map_eq_zero _).2 fun t ht => Tate.ext fun n => ?_
  have hmem : ∀ m, t.lev m ∈ (ptMap f).ker := fun m => by
    rw [MonoidHom.mem_ker, ptMap_apply, ← lev_tmap l f t m, ht]
    rfl
  have h1 : t.lev (n + N) ^ l ^ (n + N) = 1 := t.lev_pow _
  have h2 : t.lev (n + N) ^ N = 1 := hx _ (hmem _)
  have h3 : t.lev (n + N) ^ Nat.gcd (l ^ (n + N)) N = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (l ^ (n + N)) N)
  have h4 : l ^ j ≤ N := hj' ▸ Nat.le_of_dvd hN0 (Nat.gcd_dvd_right _ _)
  have h5 : j < N := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h4
  have h6 : t.lev (n + N) ^ l ^ N = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow l h5.le
    rw [hc, pow_mul, ← hj', h3, one_pow]
  show t.lev n = 1
  rw [← t.lev_add_pow n N]
  exact h6

theorem isFinite_of_tmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hf : Function.Injective (tmap l A B f)) : IsFinite f.hom.left := by
  obtain ⟨C, p, i, hp, hi, rfl⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A B f
  have hpi : Function.Injective (tmap l A C p) := by
    rw [tmap_comp, LinearMap.coe_comp] at hf
    exact hf.of_comp
  obtain ⟨hA1, hA2, hA3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hC1, hC2, hC3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl C
  have h1 : 2 * A.dim ≤ 2 * C.dim := by
    rw [← hA3, ← hC3]
    exact LinearMap.finrank_le_finrank_of_injective hpi
  have h2 : C.dim ≤ A.dim := (GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A C p).2 hp
  have h3 : A.dim = C.dim := le_antisymm (by omega) h2
  have hpf : IsFinite p.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K A C p h3 hp
  haveI := hi
  rw [comp_hom, Over.comp_left]
  infer_instance

theorem tmap_injective_of_vmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hv : Function.Injective (vmap l f)) : Function.Injective (tmap l A B f) := by
  obtain ⟨hA1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hB1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hinj : ∀ (X : AbVar K) [Module.Free ℤ_[l] (Tl l X)],
      Function.Injective (fun t : Tl l X => (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] t) := by
    intro X _
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Tl l X)
      (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    intro s t hst
    apply (TensorProduct.lid ℤ_[l] (Tl l X)).symm.injective
    apply h
    simpa using hst
  intro s t hst
  apply hinj A
  apply hv
  simp only [vmap, LinearMap.baseChange_tmul, hst]

theorem vmap_bijective_of_isIsogeny {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    Function.Bijective (vmap l f) := by
  obtain ⟨n, g, hn, -, hfg, hgf⟩ := GlobalTheory.T.exists_quasiInverse_isogeny' K A B f hf
  have hn' : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hb : ∀ (X : AbVar K), Function.Bijective (vmap l (n • 𝟙 X)) := fun X => by
    constructor
    · intro x y h
      rw [vmap_nsmul_id, vmap_nsmul_id] at h
      exact smul_right_injective _ hn' h
    · intro y
      exact ⟨(n : ℚ_[l])⁻¹ • y, by rw [vmap_nsmul_id, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  refine ⟨?_, ?_⟩
  · have h := (hb A).1
    rw [← hfg, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp
  · have h := (hb B).2
    rw [← hgf, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp

end GlobalTheory.AV.AbVar.IsogTate

namespace GlobalTheory.AV.AbVar

open IsogTate in

theorem isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime],
    (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  intro K _ l _ hl A B f
  have h1 : IsFinite f.hom.left ↔ Function.Injective (tmap l A B f) :=
    ⟨fun h => tmap_injective_of_finite_ker l f ((GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 h), isFinite_of_tmap_injective l hl f⟩
  refine ⟨h1, fun h => vmap_bijective_of_isIsogeny l f h, fun h => ?_⟩
  have hfin := h1.2 (tmap_injective_of_vmap_injective l hl f h.1)
  obtain ⟨-, -, -, hA4, hA5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨-, -, -, hB4, hB5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hd : 2 * A.dim = 2 * B.dim := by
    rw [← hA5, ← hB5]
    exact (LinearEquiv.ofBijective _ h).finrank_eq
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f (by omega) hfin⟩

end GlobalTheory.AV.AbVar
end
end

