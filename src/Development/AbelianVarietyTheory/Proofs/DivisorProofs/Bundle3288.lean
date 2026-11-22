import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticeIntegralityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_field_lattice_integrality : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
      (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A),
      X.IsPullBy X₀ (spMap R.subtype) p ∧
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) ∧
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
      ∀ (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ), IsPeriodGen X₀ U p i e a → a ≠ 0 → Sz l lam (a0 𝔣 l) (a / Ω) := by
  first | exact @GlobalTheory.LatModel.exists_model_periods | exact GlobalTheory.LatModel.exists_model_periods | (intros; apply GlobalTheory.LatModel.exists_model_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticePrimeCondition
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

set_option maxHeartbeats 1000000 in

theorem modelInt_of_latModel : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y)) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i) := by
  intro hPC hDR hDC hPM h31 E _ _ _ _ I _ d φ hd 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ hM
  obtain ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hcmC, hgen⟩ := hM
  haveI : IsDiscreteValuationRing R := hR.1
  obtain ⟨j, hj, hch, hlm, hcard, hlift, hbr⟩ := GlobalTheory.T.place_ring_fraction_embedding E l lam R hR
  haveI : CharZero R := hch
  choose φK hφK using fun i ↦ hlift (φ i)
  have hCM := GlobalTheory.T.cm_type_conjugate_in_field E (FractionRing R) j I φ φK hφK hd.2.2.2.2.2.2.1
  choose e a ha hSz hPG huniq using hgen
  have hgens : ∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
      ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i :=
    fun i ↦ ⟨ha i, hPG i, huniq i⟩
  have hL : LieExact X₀.A := (hDR.2.1 R X₀.A _ X₀.ab X₀.dim).1
  obtain ⟨n, ⟨eH⟩⟩ := GlobalTheory.DeRham.hdR_free_of_dvr hDR (FR E) 𝔠 R X₀
  obtain ⟨c₀, ψ₀, hc₀, hgen0, hpol, hCML, hr⟩ := GlobalTheory.T.divisorProofs_fact hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR
    X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens hL n eH
  obtain ⟨P, hlP, hPc⟩ := GlobalTheory.T.exists_prime_above_valuation_eq E 𝔣 l Fact.out
  obtain ⟨⟨D, hDv, hDc⟩, hDQ⟩ := h31.1 E 𝔣 h𝔣 l Fact.out R (FractionRing R) hlm hcard
  have hD0 : D ≠ 0 := by
    intro h
    have h' := hDv P hlP
    rw [h, map_zero] at h'
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp] at h'
  obtain ⟨hEig, hrest⟩ := h31.2.1 E 𝔣 h𝔣 l Fact.out Q hQ hQl R (FractionRing R) hlm hcard D hD0 hDc I
    (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) hCM (Fin n → R) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) hCML
  have hg : ∀ σ : E →+* FractionRing R, ∃ g : Fin n → R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ = Submodule.span R {g} := fun σ ↦ by
    obtain ⟨g, -, h⟩ := (hEig.2.1 σ).2.1
    exact ⟨g, h⟩
  choose gen hgen' using hg
  have hIG : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))) :=
    fun i ↦ ⟨hgen' _, hgen' _⟩
  obtain ⟨hbd, hLow, -, -⟩ := hrest _ _ hIG
  choose N hN using fun i ↦ (hLow.1 i).exists
  obtain ⟨hMex, hcomm, hprod, hskew, horth, -⟩ := hLow.2 N hN
  choose M hM using fun i ↦ (hMex i).exists
  obtain ⟨δ₀, u₀, hu₀, hu₀v⟩ := GlobalTheory.T.one_over_l_idele_character_value hDR E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK
    e a hgens D hD0 ((hDQ Q hQ hQl D).2 hDc)
  have hAdm := GlobalTheory.T.complex_multiplication_de_rham_form E (condQ 𝔣 Q) 𝔠 R (FractionRing R) X₀ cm hrm n eH ψ₀
    (fun c ψ hψ ↦ by
      obtain ⟨k, t, hk, h⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c c₀ hc₀ ψ ((2 : R) • ψ₀) hψ hpol
      refine ⟨k, 2 * t, hk, fun x y ↦ ?_⟩
      rw [h, two_mul t, map_add]
      simp [two_smul]) I D N M hM hcomm hprod hskew horth
  let e' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))
  let f' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))
  let cv : ℚ := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P
  have hDv' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) = (cv : WithTop ℚ) := hDv P hlP
  have hcv : (cv : ℝ) = c_vp 𝔣 l := hPc
  obtain ⟨m, hm⟩ : ∃ m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p, m.IsBC :=
    ⟨GlobalTheory.Published.AbelianDeRham.bcMor hp.grp, (hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1⟩
  obtain ⟨ψR, hψR⟩ := GlobalTheory.PureLift.exists_isPolForm hDR.1 X₀.ab X₀.dim (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (X₀.isLB U.c) _)
  obtain ⟨ψ, hψ, hψbc⟩ := HalfLower.exists_polForm_baseChange (algebraMap R ℂ) hp m U.c hψR
  have hf'' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := fun i ↦ by
    rw [(hIG i).2]
    exact Submodule.mem_span_singleton_self _
  have hf' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) := fun i ↦ by
    have h := hf'' i
    rwa [HalfLower.bar_bar] at h
  choose yv w hcm hyv hw using fun i ↦ GlobalTheory.T.cm_abelian_variety_good_reduction_model hDR hPC E I φ (condQ 𝔣 Q) y 𝔠 R X₀ X U p cm
    (mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ ↦ q.ne_bot)) hp hrm hcmC j hj φK hφK e a hPG hL n eH m hm i (f' i) (hf' i)
  choose ev hev using fun i ↦ hm.exists (eH.symm (e' i))
  have hDC0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
  have hpol' : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) := by
    rwa [two_smul, ← two_smul R ψ₀]
  have hsz := GlobalTheory.T.cm_auxiliary_set_abelian_galois hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens
    hL n eH c₀ ψ₀ hc₀ hgen0 hpol' hCML hr D cv hDv' hcv e' f' hIG hbd m hm ψ hψ yv ev w hcm hyv hev hw
  have hne : ∀ i, ψ (ev i) (yv i) ≠ 0 := fun i h ↦ (hsz i).1 (by rw [h]; simp)
  have hlow := fun i ↦ HalfLower.corr_lower hDR cm hrm eH hc₀ hpol hψR hD0 (hIG i).1 (hf'' i) hEig.2.2.1.2 hEig.2.2.2.2
    (hN i) (hM i) m hψbc (hev i) (hyv i) (hne i)
  have hnsm : (Fintype.card I • (cv : WithTop ℚ)) = (((Fintype.card I : ℚ) * cv : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    rw [hDv', hnsm, map_zero] at hu₀v
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
    rw [h0] at hu₀v
    exact WithTop.not_top_le_coe _ hu₀v
  obtain ⟨δ, hδ, hdet⟩ := GlobalTheory.T.periods_of_good_reduction_model hDR E I φ _ 𝔠 R X₀ X U p hp e a hPG δ₀ u₀ hu0 hu₀
  have hSz' : ∀ (x : R) (q : ℚ), x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ) →
      Sz l lam (q : ℝ) ((x : ℂ))⁻¹ := fun x q hx h ↦ by
    have := hbr _ q (HalfLower.neg_le_val_inv l x q hx h)
    rwa [map_inv₀, hj] at this
  have hpa : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha i
  let T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y) :=
    { X := X, U := U, δ := δ, C := (∏ i, a i) / (u₀ : ℂ), det := hdet, ψ := ψ, pol := hψ, y := yv, w := w,
      s := fun i ↦ (D : ℂ) / ψ (ev i) (yv i), cm := hcm }
  have hA : ∀ i, T.A i = (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 := fun i ↦ rfl
  refine ⟨𝔠, R, inferInstance, X₀, δ₀, _, T, a, fun i ↦ a i * T.A i / (D : ℂ), hR.2.1, hR.2.2.1, hAdm,
    ⟨p, m, hp, hδ, fun i x₀ x hx ↦ hlow i x₀ x hx⟩, fun i ↦ ?_, ?_⟩
  · have hA0 : T.A i ≠ 0 := by rw [hA]; exact (hsz i).1
    refine ⟨ha i, div_ne_zero (mul_ne_zero (ha i) hA0) hDC0, hA0, hSz i, (hsz i).2, ?_⟩
    have hai := ha i
    have e1 : a i * T.A i / (D : ℂ) / (a i * T.A i) = ((D : R) : ℂ)⁻¹ := by
      field_simp
    show Sz l lam (c_vp 𝔣 l) (a i * T.A i / (D : ℂ) / (a i * T.A i))
    rw [e1, ← hcv]
    exact hSz' D cv hD0 (le_of_eq hDv')
  · have e1 : T.C / ∏ i, a i = ((u₀ : R) : ℂ)⁻¹ := by
      show (∏ i, a i) / (u₀ : ℂ) / ∏ i, a i = _
      field_simp
    rw [e1]
    have h2 := hSz' u₀ ((Fintype.card I : ℚ) * cv) hu0 (by rw [hDv', hnsm] at hu₀v; exact hu₀v)
    convert h2 using 2
    push_cast
    rw [hcv]

end GlobalTheory.LatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisation_of_markedPeriods_family : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) → FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  first | exact @GlobalTheory.PELU.unif_of_fineAt | exact GlobalTheory.PELU.unif_of_fineAt | (intros; apply GlobalTheory.PELU.unif_of_fineAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatements
section
namespace GlobalTheory.Published

theorem abelianDeRhamStructure_crystallineDeRham_of_hypotheses :
    CrystallineSmoothLift → AbelianHodgeDeRham → AbelianDeRhamStructure ∧ CrystallineDeRham :=
  fun hL hH =>
    ⟨⟨GlobalTheory.Proof.abelianDeRhamFree_of_hodge hL hH, GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift hL hH,
      GlobalTheory.AbelianBaseChange.abelianDeRham_baseChange_of_smoothLift hL hH⟩,
     GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift hL⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologousStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvaturePowerSums_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, DbarCoh A (powFld A G k) (powFld A G' k) := by
  first | exact @GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | exact GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | (intros; apply GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_primeToP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (exact GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (intros; apply GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.PerPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_nat_smul_mem {N : ℕ} (X : Data E N) (v : Fin N → E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem X v

theorem perFr_natCast_smul {N : ℕ} (X : Data E N) (x : Frame X.Ψ N) (v : Fin N → E) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x ((n : E) • v) τ i = (n : ℂ) * perFr X x v τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ ((n : E) • v) = (n : ℂ) • Data.emb τ v := fun τ => funext fun a => by
    simp [Data.emb, map_natCast]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v R
  obtain ⟨n, hn, hnv⟩ := exists_nat_smul_mem (U.X k) v
  obtain ⟨C₁, B, h₁⟩ := GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
    _ hnv R
  obtain ⟨C₃, h₃⟩ : ∃ C₃ : ℝ, ∀ᶠ w in imTop, (U.X k).p0 = 0 → ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := by
    by_cases h0 : (U.X k).p0 = 0
    · obtain ⟨C₃, h⟩ := GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
        h0 v
      exact ⟨C₃, h.mono fun w hw _ => hw⟩
    · exact ⟨0, .of_forall fun w h => absurd h h0⟩
  have him : ∀ᶠ w in imTop, 1 ≤ w.im :=
    (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_ge_atTop 1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨max (C₁ / n) 0 + max C₃ 0, B, ?_⟩
  filter_upwards [h₁, h₃, him] with w hw1 hw3 hwi hR τ i
  have hpow : 1 ≤ w.im ^ B := one_le_pow₀ hwi
  have hK0 : 0 ≤ max (C₁ / n) 0 + max C₃ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hK1 : C₁ / n ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hK3 : C₃ ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hlat : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := by
    intro τ i h
    have h2 := hw1 hR τ i h
    rw [perFr_natCast_smul, norm_mul, Complex.norm_natCast] at h2
    have h3 : ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₁ / n * w.im ^ B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn']
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have hzero : 0 ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := mul_nonneg hK0 (by positivity)
  by_cases hτ : τ ∈ (U.X k).Ψ
  · by_cases hi : i < N - (U.X k).p0
    · exact hlat τ i (Or.inl ⟨hτ, hi⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dif_pos hτ, dif_neg (by omega)]
      rw [e, norm_zero]
      exact hzero
  · by_cases hc : conjEmb τ ∈ (U.X k).Ψ
    · by_cases h0 : (U.X k).p0 = 0
      · calc ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := hw3 h0 τ i hτ
          _ ≤ max (C₁ / n) 0 + max C₃ 0 := hK3
          _ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := le_mul_of_one_le_right hK0 hpow
      · by_cases hi : i < (U.X k).p0
        · exact hlat τ i (Or.inr ⟨hc, hi⟩)
        · have e : perFr (U.X k) (xx w) v τ i = perFr (U.X k) (xx w) v τ ((U.X k).p0 - 1) := by
            have e1 : (U.X k).p0 - 1 - i = (U.X k).p0 - 1 - ((U.X k).p0 - 1) := by omega
            unfold perFr
            rw [dif_neg hτ, dif_neg hτ, dif_pos hc, dif_pos hc]
            simp only [e1]
          rw [e]
          exact hlat τ _ (Or.inr ⟨hc, by omega⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dif_neg hτ, dif_neg hc]
      rw [e, norm_zero]
      exact hzero

end GlobalTheory.ShFam.PerPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem eq_of_secRatioEq_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, H⟩ := GlobalTheory.T.exists_section_ratios_generate_mod_maximal R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨N, m, σ, r, hwN, hNaff, hNi, hgerm, hgen⟩ := H e k hk s₀ i w hw hu
  have hw' : (fstG (maximalIdeal R) e G).left ≫ G.hom = (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e :=
    (fstG (maximalIdeal R) e G).w
  have hz : ∀ x ∈ maximalIdeal R ^ (e + 1), (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) x = 0 := by
    intro x hx
    have h0 : (thick R (maximalIdeal R) e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, hw', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, h0, map_zero]
  have hgen' := GlobalTheory.T.localized_presentation_eval_quotient_fraction R _ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) (e + 1) hz m r hgen
  refine ⟨N, m, σ, hwN, fun W a b hab ha hb hrat => ?_⟩
  have ha' : ⊤ ≤ a ⁻¹ᵁ N := fun x _ => ha x
  have hb' : ⊤ ≤ b ⁻¹ᵁ N := fun x _ => hb x
  have hst : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (f : Γ((thickObj R (maximalIdeal R) e G).left, N)), c x ∈ N →
      (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) = gs c x N f := by
    intro c x f h
    have e1 : gs (c ≫ 𝟙 _) x N f = (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) := by
      rw [gs_eq (𝟙 _) (c x) _ h, ← gs_pull c (𝟙 _) x _ h, gs_eq c x _ (show c x ∈ (𝟙 (thickObj R (maximalIdeal R) e G).left : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) ⁻¹ᵁ N from h)]
      exact (Scheme.Hom.germ_stalkMap_apply c _ x h _).symm
    rw [← e1, Category.comp_id]
  have hsg : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (s : H0 U.LG.L k), c x ∈ N →
      secGerm (c ≫ (fstG (maximalIdeal R) e G).left) x s i = (c.stalkMap x).hom (secGerm (fstG (maximalIdeal R) e G).left (c x) s i) :=
    fun c x s h => secGerm_comp c _ x s (hNi h)
  refine GlobalTheory.T.eq_of_agree_on_affineOpen_generators R _ W ((fstG (maximalIdeal R) e G).left ≫ G.hom) N hNaff m r hgen' a b ?_ ha' hb' ?_
  · rw [hw', ← Category.assoc, hab, Category.assoc]
  · intro l
    apply fn_ext
    intro x _
    rw [gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_pull (𝟙 W) a x N (ha x), gs_pull (𝟙 W) b x N (hb x), Category.id_comp, Category.id_comp]
    have key := secRatioEq_iff_germ.1 (hrat l) x i i (hNi (ha x)) (hNi (hb x))
    rw [hsg a x _ (ha x), hsg a x _ (ha x), hsg b x _ (hb x), hsg b x _ (hb x),
      (hgerm _ (ha x)).2 l, (hgerm _ (hb x)).2 l, map_mul, map_mul, hst a x _ (ha x), hst b x _ (hb x)] at key
    have hA := ((hgerm _ (ha x)).1).map (a.stalkMap x).hom
    have hB := ((hgerm _ (hb x)).1).map (b.stalkMap x).hom
    refine (hA.mul hB).mul_left_inj.1 ?_
    linear_combination key

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevels
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem eq_zero_of_ev_cube : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  intro p k _ d G c
  have hnil : ∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i) := by
    intro n i
    cases i with
    | inl i => exact (c.nil n i).map (Algebra.TensorProduct.includeLeft (R := k) (S := k))
    | inr j => exact (c.nil₂ n j).map (Algebra.TensorProduct.includeRight (R := k))
  refine ⟨hnil, fun f hf => ?_⟩
  ext α
  obtain ⟨n, hn⟩ := c.presents.2 (α.degree + 1)
  have hs := c.presents.1 n
  have h2 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n) (c.nil n)
    (c.nil₂ n) hs hs
  have h3 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d ⊕ Fin d) (G.A n) (G.A n ⊗[k] G.A n) (c.x n) (c.nil n)
    (c.x₂ n) (c.nil₂ n) (hnil n) hs h2.1
  have := (h3.2 (α.degree + 1) hn (h2.2 (α.degree + 1) hn hn) f (hf n (hnil n)) α (Nat.lt_succ_self _))
  simpa using this

end GlobalTheory.Katz.Chart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosedField_torsionMaps_commute_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  first | exact @GlobalTheory.Mum.Two.exists_key | exact GlobalTheory.Mum.Two.exists_key | (intros; apply GlobalTheory.Mum.Two.exists_key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechClass_of_quasiPeriodic_holomorphic_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.OfCover.exists_isPer | exact GlobalTheory.CechPer.OfCover.exists_isPer | (intros; apply GlobalTheory.CechPer.OfCover.exists_isPer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedFibre_theta_embedding_of_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  first | exact @GlobalTheory.Mum.SecEmb.emb_of_secs | exact GlobalTheory.Mum.SecEmb.emb_of_secs | (intros; apply GlobalTheory.Mum.SecEmb.emb_of_secs <;> assumption)
end

