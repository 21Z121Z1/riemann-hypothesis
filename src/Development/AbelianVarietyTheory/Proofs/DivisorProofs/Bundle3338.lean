import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClasses
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeArithVariety
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.LineBundleBaseChange

theorem residueDegree_fst_ne_zero {X Y₁ Y₂ : Scheme.{0}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (z : ↥(pullback f g))
    (h : g.residueDegree (pullback.snd f g z) ≠ 0) : (pullback.fst f g).residueDegree z ≠ 0 := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite g _).1 h).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  let s : PrimeSpectrum T.tensor := Scheme.Pullback.SpecOfPoint z
  have hs : T.SpecTensorTo s = z := Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  have hm : s.asIdeal.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' T.tensorInl.hom hl.to_isIntegral s.asIdeal ?_
    have hp : (s.asIdeal.comap T.tensorInl.hom).IsPrime := inferInstance
    rw [Ideal.eq_bot_of_prime (s.asIdeal.comap T.tensorInl.hom)]
    exact Ideal.bot_isMaximal
  letI := Ideal.Quotient.field s.asIdeal
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ s.asIdeal) := CommRingCat.ofHom (Ideal.Quotient.mk s.asIdeal)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ s.asIdeal)) := (⊥ : PrimeSpectrum (T.tensor ⧸ s.asIdeal))
  have hq : Spec.map ρ q = s := PrimeSpectrum.ext Ideal.mk_ker
  have e : (Spec.map ρ ≫ T.SpecTensorTo) q = z := by
    rw [Scheme.Hom.comp_apply, hq, hs]
  rw [← e]
  refine PullbackFinitePoint.residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
  rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]

theorem map_genericPoint_of_mem {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : f (genericPoint X) = genericPoint Y :=
  ((h ▸ (genericPoint_specializes x).map f.continuous : f (genericPoint X) ⤳ genericPoint Y).antisymm
    (genericPoint_specializes _)).eq

theorem main : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral B']
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p)
    (E : B.Modules), GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ g : B' ⟶ B, IsArithVar (g ≫ q) d →
    g (genericPoint B') = genericPoint B → g.residueDegree (genericPoint B') ≠ 0 →
    ∃ (_ : IsIntegral (pullback π g : Scheme.{0})), IsArithVar (pullback.fst π g ≫ p) (d + 1) ∧
      pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y ∧
      (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0 := by
  intro k _ B Y B' _ _ _ q p d hq hp π w E hE fl hfl g hg hgen hdeg
  subst w
  have := hg.isLocallyNoetherian
  have hfl' := GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl
  have hE' : ∀ _ : Unit, GlobalTheory.VB.IsVB ((Scheme.Modules.pullback g).obj E) 2 := fun _ => hE.pullback g
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd π g) := by
    simpa using GlobalTheory.T.flag_bundle_smooth_relative_dimension B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs' := GlobalTheory.T.flag_bundle_projection_surjective B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs := GlobalTheory.T.flag_bundle_projection_surjective B Y π Unit _ _ _ (fun _ => hE) hfl
  have := GlobalTheory.T.flag_bundle_total_space_irreducible B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd π g)
  have := GlobalTheory.geometricallyReduced_of_smooth (pullback.snd π g)
  have := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd π g)
  have hI : IsIntegral (pullback π g : Scheme.{0}) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hπ : π (genericPoint Y) = genericPoint B := by
    obtain ⟨y, hy⟩ := hs (genericPoint B)
    exact map_genericPoint_of_mem π y hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) _ _ (hπ.trans hgen.symm)
  refine ⟨hI, ⟨hq.isDomain, hq.finite, hI, ?_, ?_, ?_⟩, map_genericPoint_of_mem _ z hz₁,
    residueDegree_fst_ne_zero π g _ ?_⟩
  · have : IsSeparated q := by
      obtain ⟨N, j, _, rfl⟩ := hq.isProjOver
      have := isProper_str k N
      infer_instance
    have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc π g q)
      (ProjSpace.isProjOver_pullback hp.isProjOver hg.isProjOver)
    rwa [pullback.lift_fst_assoc, Category.comp_id] at h
  · rw [← Category.assoc (pullback.fst π g), pullback.condition, Category.assoc (pullback.snd π g),
      Category.assoc (pullback.snd π g)]
    have := hg.flat
    infer_instance
  · exact GlobalTheory.T.krull_dim_smooth_surjective_total B' _ (pullback.snd π g) 1 d hs' hg.dim_eq
  · rw [map_genericPoint_of_mem _ z hz₂]
    exact hdeg

end GlobalTheory.LineBundleBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveQuotientLineStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_successive_quotient_line : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (wσ : ρ ≫ σ = π) (S P E₁ : Y₁.Modules) (s : S ⟶ P)
      (j : P ⟶ (Scheme.Modules.pullback σ).obj (E a)) (t : P ⟶ E₁) (wst : s ≫ t = 0)
      (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (A₀ A₁ : (Σ b, Fin (r b)) → Y₁.Modules)
      (u : ∀ z, A₀ z ⟶ A₁ z) (v : ∀ z, A₁ z ⟶ (Scheme.Modules.pullback σ).obj (E z.1)),
      IsIntegral Y₁ ∧ IsProjOver (σ ≫ q) ∧ Surjective ρ ∧ topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 ∧
      IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (ShortComplex.mk s t wst).ShortExact ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧ GlobalTheory.VB.IsVB S i ∧
      GlobalTheory.VB.IsVB P ((i : ℕ) + 2) ∧ GlobalTheory.VB.IsVB E₁ 2 ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ (fl a).F i'.succ, e.hom ≫ (fl a).ι i'.succ =
        (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ (fl a).F i.castSucc, e.hom ≫ (fl a).ι i.castSucc =
        (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ (x : (fl a).F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : (fl a).F i.succ ⟶ fl₁.F 1),
        x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a) = (fl a).ι i.succ ∧
        g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) ∧
      ∀ z : Σ b, Fin (r b), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle (u z) ∧ GlobalTheory.VB.IsSubbundle (v z) ∧ GlobalTheory.VB.IsVB (A₀ z) z.2 ∧
        GlobalTheory.VB.IsVB (A₁ z) ((z.2 : ℕ) + 1) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₁ z) ≅ (fl z.1).F z.2.succ, e.hom ≫ (fl z.1).ι z.2.succ =
          (Scheme.Modules.pullback ρ).map (v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₀ z) ≅ (fl z.1).F z.2.castSucc, e.hom ≫ (fl z.1).ι z.2.castSucc =
          (Scheme.Modules.pullback ρ).map (u z ≫ v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) := by
  first | exact @GlobalTheory.OmitStep.omitStep_bundle | exact GlobalTheory.OmitStep.omitStep_bundle | (intros; apply GlobalTheory.OmitStep.omitStep_bundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.TateCompare
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKGeo.GammaUniq

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem exists_simSys_all {N : ℕ} (hN : 0 < N) (hK : N.Coprime p) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ n q q' z z', e n q q' z → e n q q' z' → z = z') (I₁ I₂ : TateIsoO D k Q act e)
    (hI : ∀ y, I₁.ev N y = I₂.ev N y) :
    ∃ t : SimSys D N N, ∀ n, 0 < n → n.Coprime p → ∀ y, I₂.ev n y = I₁.ev n (t.g n y) := by
  choose g hg using exists_lift I₁ I₂
  choose u hu using exists_mult I₁ I₂
  have hdiv : ∀ {n m : ℕ}, (n * m).Coprime p → n.Coprime p := fun {n m} h =>
    Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) h
  have utow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n] := by
    intro n m hn hm hc
    have h : I₁.ζ n ^ u (n * m) = I₁.ζ n ^ u n := by
      rw [hu n hn (hdiv hc), ← I₂.ζ_pow n m hn hm hc, ← hu _ (Nat.mul_pos hn hm) hc, ← pow_mul, mul_comm (u _) m,
        pow_mul, I₁.ζ_pow n m hn hm hc]
    rwa [pow_eq_pow_iff_modEq, ← (I₁.ζ_prim n hn (hdiv hc)).eq_orderOf] at h
  have gtow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    rw [← ev_eq_iff I₁ hn (hdiv hc), hg n hn (hdiv hc), ← I₁.tower n m hn hm hc, hg _ (Nat.mul_pos hn hm) hc,
      I₂.tower n m hn hm hc]
  have sim2 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y,
      (n : ℤ) ∣ 2 * (D.EF (g n x) (g n y) - u n * D.EF x y) := by
    intro n hn hc x y
    have h₁ := I₁.isom n hn hc (g n x) (g n y)
    rw [hg n hn hc, hg n hn hc] at h₁
    have h := he _ _ _ _ _ h₁ (I₂.isom n hn hc x y)
    rw [← hu n hn hc, ← zpow_natCast, ← _root_.zpow_mul] at h
    rw [← (I₁.ζ_prim n hn hc).zpow_eq_one_iff_dvd, mul_sub, _root_.zpow_sub, h,
      show (u n : ℤ) * (2 * D.EF x y) = 2 * (u n * D.EF x y) by ring, mul_inv_cancel]
  refine ⟨{
    g := g
    u := u
    lin := fun n hn hc c x => ?_
    u_cop := fun n hn hc => ?_
    u_tower := utow
    surj := fun n hn hc x => ?_
    inj := fun n hn hc x z h => ?_
    sim := fun n hn hc x y => ?_
    tower := gtow
    one := fun x => ?_ }, fun n hn hc y => (hg n hn hc y).symm⟩
  · rw [← ev_eq_iff I₁ hn hc, hg n hn hc, I₁.lin, I₂.lin, hg n hn hc]
  · rw [← (I₁.ζ_prim n hn hc).pow_iff_coprime hn, hu n hn hc]
    exact I₂.ζ_prim n hn hc
  · obtain ⟨y, hy⟩ := (I₂.onto n hn hc _).1 ((I₁.onto n hn hc _).2 ⟨x, rfl⟩)
    refine ⟨y, ?_⟩
    rw [← ev_eq_iff I₁ hn hc, hg n hn hc, hy]
  · rw [← I₂.ker n hn hc, ← hg n hn hc, h]
    exact I₁.ev_nsmul_self hn hc z
  · by_cases hp : p = 2
    · subst hp
      have hco : IsCoprime (n : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hc
      exact hco.dvd_of_dvd_mul_left (sim2 n hn hc x y)
    · have hc2 : (n * 2).Coprime p :=
        Nat.Coprime.mul_left hc ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
      have h := sim2 (n * 2) (by omega) hc2 x y
      obtain ⟨z, hz⟩ := gtow n 2 hn two_pos hc2 x
      obtain ⟨w, hw⟩ := gtow n 2 hn two_pos hc2 y
      obtain ⟨a, ha⟩ := (utow n 2 hn two_pos hc2).dvd
      obtain ⟨c, hcc⟩ := h
      rw [hz, hw] at hcc
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hcc
      push_cast at hcc
      refine ⟨c - D.EF (g n x) w - D.EF z (g n y) - n * D.EF z w - a * D.EF x y, ?_⟩
      have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hcc - 2 * D.EF x y * ha
  · rw [← ev_eq_iff I₁ hN hK, hg N hN hK, hI]

theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem isIntAf_intCast (c : ℤ) : IsIntAf (c : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ c

theorem inAf_mem (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : a • z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_mem (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (hA : ∀ x, A (inAf D x) ∈ LaHat D)
    {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : A z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = c • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul]
    exact smul_mem hc (hA x)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem eq_zero_of_dvd (a : AfP p) (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ c, IsIntAf c ∧ a = n • c) : a = 0 := by
  have key : ∀ v : AwayP p, AfP.eval v a = 0 := by
    intro v
    by_contra hne
    obtain ⟨l, hl0, hlp, hlv⟩ : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
      have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
      have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
      have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
      obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
      have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
      refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
      · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
      · rcases Int.natAbs_eq x with h1 | h1
        · rw [← h1]; exact hx
        · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx
    have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
      have e : ((l : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ) := by simp
      have e2 : Valued.v (algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ)) = v.1.valuation ℚ (algebraMap ℤ ℚ (l : ℤ)) := by
        rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
        exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
      rw [e, e2, HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hlv
    have hv0 : Valued.v (AfP.eval v a) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
    obtain ⟨c, hc, e⟩ := h (l ^ j) (pow_pos hl0 j) (Nat.Coprime.pow_left j hlp)
    have hc1 : Valued.v (AfP.eval v c) ≤ 1 := hc v
    have : Valued.v (AfP.eval v a) ≤ Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) ^ j := by
      rw [e, map_nsmul, nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow]
      exact mul_le_of_le_one_right' hc1
    exact absurd hj (not_lt.2 this)
  exact Subtype.ext (funext key)

def basAf {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem basAf_apply {J : Type} (b : Module.Basis J ℤ D.La) (i : J) : basAf b i = inAf D (b i) := by
  simp [basAf, inAf]

theorem isIntAf_repr {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) :
    IsIntAf ((basAf b).repr z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (basAf b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [basAf, Algebra.smul_def]
    rw [e]
    exact isIntAf_mul (isIntAf_intCast _) hc
  | zero => simpa using isIntAf_intCast (p := p) 0
  | add x y _ _ hx hy =>
    intro v
    rw [map_add, Finsupp.add_apply, map_add]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem eq_zero_of_dvd_laHat (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := by
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  refine (basAf b).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_dvd _ fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := h n hn hc
  exact ⟨_, isIntAf_repr b i hw, by rw [map_nsmul, Finsupp.smul_apply]⟩

theorem end_ext {A B : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : ∀ x, A (inAf D x) = B (inAf D x)) : A = B := by
  have := D.freeLa
  exact (basAf (Module.Free.chooseBasis ℤ D.La)).ext fun i => by rw [basAf_apply, h]

theorem actOn_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hr : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  have h₁ : Function.Injective (rep.toLinearMap.lTensor R) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hr
  have j := (TensorProduct.isBaseChange ℚ V R).end
  have e : ∀ x, actOn rep R x = j.equiv (rep.toLinearMap.lTensor R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul]
      ext v
      have := (TensorProduct.isBaseChange ℚ V R).endHom_comp_apply (rep c) v
      have e₁ : actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
        rw [Algebra.smul_def]; rfl
      rw [e₁]
      simp at this ⊢
      simp [this, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y h
  rw [e, e] at h
  exact h₁ (j.equiv.injective h)

variable {G : HTGroup p} (L : Link D G)

theorem actG_injective : Function.Injective L.actG := by
  intro g h e
  have := D.finLa
  have h₁ : (g.1.1 : AfP p ⊗[ℚ] G.C) = h.1.1 := actOn_injective L.rep L.rep_inj (AfP p) e
  have h₁' : g.1.1 = h.1.1 := Units.ext h₁
  refine Subtype.ext (Prod.ext h₁' (Units.ext ?_))
  have hg := mem_uGroup.1 g.2
  have hh := mem_uGroup.1 h.2
  rw [h₁, hh] at hg
  have hinj : Function.Injective (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    Algebra.TensorProduct.includeLeft_injective (S := ℚ) (algebraMap ℚ G.C).injective
  exact (hinj hg).symm

theorem inAf_add (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf, TensorProduct.tmul_add]

end GlobalTheory.LKGeo.GammaUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClassesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ B : GlobalTheory.LKDef.DForm G,
      B.trace ξ L.K.toSubgroup f K' f' =
        ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G B.β),
          LinearMap.trace ℂ V (ξ (Quotient.out c : GlobalTheory.LKCx.grp G B.β).1) *
            centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c) := by
  first | (exact @GlobalTheory.HeckeTrace.dform_trace_eq) | (exact GlobalTheory.HeckeTrace.dform_trace_eq) | (intros; apply GlobalTheory.HeckeTrace.dform_trace_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClassesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_geom | exact GlobalTheory.BCT.trOn_forms_hop_eq_geom | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_geom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOfAlgebraicModelStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_of_algebraic_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  first | exact @GlobalTheory.LatModel.modelInt | exact GlobalTheory.LatModel.modelInt | (intros; apply GlobalTheory.LatModel.modelInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P) (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q → IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) → IsClosed (q '' closure C) := by
  first | exact @GlobalTheory.FibProperClosed.isClosed_image_closure | exact GlobalTheory.FibProperClosed.isClosed_image_closure | (intros; apply GlobalTheory.FibProperClosed.isClosed_image_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetricStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  first | exact @GlobalTheory.ChernCalc.isForm_evalF_chernF | exact GlobalTheory.ChernCalc.isForm_evalF_chernF | (intros; apply GlobalTheory.ChernCalc.isForm_evalF_chernF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegreeStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  first | exact @GlobalTheory.Dieu.isIsog_hasLogDeg_map | exact GlobalTheory.Dieu.isIsog_hasLogDeg_map | (intros; apply GlobalTheory.Dieu.isIsog_hasLogDeg_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjectiveStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_ge_finrank_of_semilinear_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U] [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U), Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) → ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) → (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧ ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  first | exact @GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | exact GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | (intros; apply GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearUniformisation_pullback_localHom : ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (θ : R →+* V), Base R → Base V → IsLocalHom θ → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap θ (genericPoint (Sp V)) ∈ W → ∃ (D₁ : DegData V (maximalIdeal V)) (hD : IsPullDeg θ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing V))) (U₁ : Unif (maximalIdeal V) D₁ A₁ ((Over.pullback (specOf θ)).obj G)) (_ : Module O D₁.toPre.X) (o₁ : D₁.toPre.OAct O) (oA₁ : A₁.OAct O) (oG₁ : RingAct ((Over.pullback (specOf θ)).obj G) O), LBIso U₁.LG.L (U.LG.L.pull (pullback.fst G.hom (specOf θ))) ∧ (∀ (a : O) (y : D₁.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (o.onB.act a).left) ∧ (∀ a, oG₁.act a = (Over.pullback (specOf θ)).map (oG.act a)) ∧ U₁.toUnifPre.OLinear O o₁ oA₁ oG₁ := by
  first | exact @GlobalTheory.Mum.ulin_pull | exact GlobalTheory.Mum.ulin_pull | (intros; apply GlobalTheory.Mum.ulin_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordSectionsMultiplierThickeningsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordSections_multiplier_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, 3 ≤ k → ∃ S : H0 U.LG.L k → H0 U.LG.L (N * k), ∃ c : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'), (∀ (e : ℕ) (s : H0 U.LG.L k) (i i' : Fin 1 → U.LG.L.ι), ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_right : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')).op).hom (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((S s).f i')) = c e i i' * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i') := by
  first | exact @GlobalTheory.MumMult.main | exact GlobalTheory.MumMult.main | (intros; apply GlobalTheory.MumMult.main <;> assumption)
end

