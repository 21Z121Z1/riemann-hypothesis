import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumCoc
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.diagSum_coc : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (N : ℕ), (p : R) ^ N = 0 → diagSum R (G.A N) (p ^ N) (d.coc N) = chi (p ^ N) d.g (G.A N) (t.y N) := by
  intro R _ A _ p G t c d N hN
  let e : ℕ → (G.A N →ₐ[R] G.A N) := fun j ↦ (toConv (AlgHom.id R (G.A N)) ^ j).ofConv
  let K : ℕ → G.A N := fun j ↦ fv d.f (G.A N) (G.A N) (e j) (t.y N) + e j (d.h N)
  have hm : ∀ j, (mulBy R (G.A N) j : G.A N →ₐ[R] G.A N) = e j := fun j ↦ by
    have h := comp_mulBy_pts (AlgHom.id R (G.A N)) j
    rwa [AlgHom.id_comp] at h
  have hy : ∀ j, spOver (e j) ≫ t.y N = t.y N ^ j := fun j ↦ by
    rw [← hm]; exact t.mulBy_y N j
  have he1 : e 1 = AlgHom.id R (G.A N) := by simp only [e, pow_one, ofConv_toConv]
  have hes : ∀ i, (toConv (e i) * toConv (AlgHom.id R (G.A N))).ofConv = e (i + 1) := fun i ↦ by
    simp only [e, toConv_ofConv, pow_succ]
  have hterm : ∀ i, Algebra.TensorProduct.lift (mulBy R (G.A N) i : G.A N →ₐ[R] G.A N) (AlgHom.id R (G.A N))
      (fun _ _ ↦ Commute.all _ _) (d.coc N) = d.g (G.A N) (t.y N ^ i) (t.y N) - (K (i + 1) - K i - K 1) := by
    intro i
    rw [hm i, Dat.lift_coc R A p G t c d N (G.A N) (e i) (AlgHom.id R _), hy, spOver_id, Category.id_comp, hes]
    simp only [K, he1]
  have hq : e (p ^ N) = e 0 := t.inj N (G.A N) _ _ (by rw [hy, hy, t.y_pow, pow_zero])
  have hz : ((p ^ N : ℕ) : G.A N) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap R (G.A N)), ← map_pow, hN, map_zero]
  rw [diagSum, LinearMap.sum_apply]
  simp only [AlgHom.toLinearMap_apply, hterm]
  rw [chi, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ K j), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hz, zero_mul, sub_zero]
  have : K (p ^ N) = K 0 := by simp only [K, hq]
  rw [this, sub_self, sub_zero]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUniqueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalSiegel_heisenbergInvariant_form_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  first | exact @GlobalTheory.DiagSiegelUniq.uniq | exact GlobalTheory.DiagSiegelUniq.uniq | (intros; apply GlobalTheory.DiagSiegelUniq.uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrDiv

theorem dvd_of_forall_cDvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, ht⟩ := h W hW φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

end GlobalTheory.DvrDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOrdSub
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.TauFormGen

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem dvd_ord_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G')
  (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing V) F (gK x)) →
  ∀ (k : ℕ), IsUnit (k : R) → ∀ (ϖ : V), Irreducible ϖ → ∀ (O : ValuationSubring F) (φ : V →+* O) (σ : F →ₐ[FractionRing V] F) (π : F), IsLocalHom φ →
    (∀ w, (φ w : F) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) → (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    π ^ k = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ) → IsPrimitiveRoot (σ π / π) k →
  ∀ (ρ : D.toPre.X →+ D'.toPre.X) (e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A)),
    (∀ (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) →
    (∀ (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) →
    (∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ) (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a') →
  ∀ (a b : D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre (ρ a) (ρ b) x' →
    (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ _ hVb G' _ _ hG' D' A' U' g gK hgK F _ _ _ _ hF k hk ϖ hϖ O φ σ π hφ eφ hσ
    hπ hζ ρ e hW hGal hT a b x x' hx hx'
  obtain ⟨hR, _⟩ := hRb
  obtain ⟨hV, _⟩ := hVb
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV D' A' G' hG' U' F k hk1
  have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have wt₂ : ∀ (p p' : QkPt D'.toPre F k) (τ : Multiplicative D'.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A'.A A'.L (k : ℤ) (f' p) (f' p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₂ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have c₁ : ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' →
      (f p').left = spMap σ.toRingHom ≫ (f p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f p)
    have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
    rw [← this, hy]
  have c₂ : ∀ (σ : F →ₐ[FractionRing V] F) p p', QkExt σ.toRingHom p p' →
      (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds V (maximalIdeal V) hV D' A' G' hG' U' F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f' p)
    have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
    rw [← this, hy]
  have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
      WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
    GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'
  have tor : ∀ (τ' : Multiplicative D'.toPre.X →* Fˣ) (q' : QkPt D'.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt D.toPre F k,
      WeilIs A.A A.L (k : ℤ) (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') :=
      hT _ τ' q q' (f q) (f' q') h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hw := wt₁ q p (τ'.comp (AddMonoidHom.toMultiplicative ρ)) h₄ h₅
    rw [this] at hw
    exact hw
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    have h := hW _ _ _ (wt₂ q' p' τ' h₂ h₃)
    rw [← hp] at h
    exact uniq _ _ _ _ (tor τ' q' h₁ h₂ h₃ p) h

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor V _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart V _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, hGal (f' p') (f' r') (c₂ σ p' r' hr'), ← hp])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
    have h := tor τ₂ q₂ k₂ y₂ t₂ pb
    rw [← hq] at h
    exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord V F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main V _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw V).map_mul, (ord_vw V).map_unit, (ord_vw V).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

end GlobalTheory.TauFormGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro p _ V _ _ _ i hloc hi x
  have hV : ValuationRing V := inferInstance
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := fun h => hnot ⟨0, by simp [h]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩
    · exact hnot ⟨a, ha⟩
    · have hwu : ¬ IsUnit w := by
        intro hu
        apply hnot
        refine ⟨(hu.unit⁻¹ : Vˣ), ?_⟩
        have h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1 := by
          rw [← map_mul]; simp
        rw [hw] at h1
        exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)
      have hiw : ¬ IsUnit (i w) := fun h => hwu (IsLocalHom.map_nonunit w h)
      have hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw
      have hlw : IsFractionRing.lift (K := FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by
        rw [← hw, IsFractionRing.lift_algebraMap]; rfl
      have hprod : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by
        rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
      rw [hlw] at hprod
      have : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=
        calc _ ≤ 1 * ‖((i w : OO p) : PadicAlgCl p)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [_root_.one_mul]; exact hlt
      linarith
  · rintro ⟨v, rfl⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (GlobalTheory.ZH.mem_OO_iff _).1 (i v).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

open GlobalTheory.Mum.Pow8

section Pairing

theorem comp_matAct_pr {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {X : Over S}
    (x : X ⟶ powObj G₀ 8) (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) :
    (x ≫ matAct G₀ a) ≫ powPr G₀ i = ∏ j, (x ≫ powPr G₀ j) ^ a i j := by
  rw [Category.assoc, matAct_pr]
  exact GlobalTheory.Mum.TensAct.comp_prod_zpow x _ _

variable {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {L : LB G₀.left} (hL : L.IsLB)

def formPair (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) : GlobalTheory.CechPic.Pic X.left :=
  ∑ i, ∑ j, M i j • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ i) (y ≫ powPr G₀ j)

theorem cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) :
    GlobalTheory.CechPic.cls _ h = formPair hL W (𝟙 _) (𝟙 _) := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold formPair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, lamPts, negε, GlobalTheory.CechPic.lam, Category.id_comp]
  simp [smul_add, sub_eq_add_neg]

theorem pull_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S} (u : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls _ h) = formPair hL W u u := by
  rw [cls_e8LB hL W h]
  unfold formPair
  simp only [map_sum, map_zsmul, GlobalTheory.CechPic.pull_lam, Category.id_comp]

variable (hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ L), t.IsGen)
include hΘ

theorem formPair_mul (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (u v : X ⟶ powObj G₀ 8) :
    formPair hL M (u * v) (u * v) = formPair hL M u u + formPair hL M v v + formPair hL (M + M.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ powPr G₀ i = (u ≫ powPr G₀ i) * (v ≫ powPr G₀ i) := fun i => MonObj.mul_comp _ _ _
  have e1 : ∀ i j, GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) ((u * v) ≫ powPr G₀ i) ((u * v) ≫ powPr G₀ j) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (u ≫ powPr G₀ j) +
        GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (v ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
        (GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
          GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ j) (v ≫ powPr G₀ i)) := by
    intro i j
    rw [hm, hm, GlobalTheory.CechPic.lam_mul_left hL hΘ, GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ,
      GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ, GlobalTheory.CechPic.lam_comm _ (v ≫ powPr G₀ i) (u ≫ powPr G₀ j)]
    abel
  unfold formPair
  simp only [e1, smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul, Matrix.transpose_apply]
  congr 2
  exact Finset.sum_comm

theorem formPair_one (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} :
    formPair hL M (1 : X ⟶ powObj G₀ 8) 1 = 0 := by
  unfold formPair
  simp [MonObj.one_comp, GlobalTheory.CechPic.lam_one_left]

theorem lam_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S}
    (x y : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ h) x y = formPair hL (W + W.transpose) x y := by
  unfold GlobalTheory.CechPic.lam
  simp only [pull_cls_e8LB hL W h]
  rw [formPair_mul hL hΘ, formPair_one hL hΘ]
  abel

theorem formPair_act_left (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M (x ≫ matAct G₀ a) y = formPair hL (a.transpose * M) x y := by
  have s3 : ∀ F : Fin 8 → Fin 8 → Fin 8 → GlobalTheory.CechPic.Pic X.left,
      ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := fun F =>
    calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_left hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  refine (s3 (fun i j k => (M i j * a i k) •
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ k) (y ≫ powPr G₀ j))).trans ?_
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [mul_comm]

theorem formPair_act_right (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M x (y ≫ matAct G₀ a) = formPair hL (M * a) x y := by
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_right hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Pairing

theorem unimodular_symmetrised_matrix_adjugate_identities {W : Matrix (Fin 8) (Fin 8) ℤ} (hB : (W + W.transpose).det = 1) :
    (W + W.transpose) * ((W + W.transpose).adjugate * W) = W ∧
      (W + W.transpose).adjugate * W + (W + W.transpose).adjugate * W.transpose = 1 ∧
      ((W + W.transpose).adjugate * W).transpose * (W + W.transpose) =
        (W + W.transpose) * ((W + W.transpose).adjugate * W.transpose) := by
  have hBt : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by
    rw [Matrix.mul_adjugate, hB, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by
    rw [Matrix.adjugate_mul, hB, one_smul]
  have hAt : (W + W.transpose).adjugate.transpose = (W + W.transpose).adjugate := by
    rw [Matrix.adjugate_transpose, hBt]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · rw [← Matrix.mul_add, h2]
  · rw [Matrix.transpose_mul, hAt, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hypW_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀)
    (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  intro S G₀ _ _ P W hW
  have hL : P.L.L.IsLB := P.L.isLB
  have hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ P.L.L), t.IsGen := ⟨P.c.1, P.c.2⟩
  have hE : (e8LB G₀ P.L.L W).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨h1, h2, h3⟩ := unimodular_symmetrised_matrix_adjugate_identities hW.2
  refine ⟨matAct G₀ ((W + W.transpose).adjugate * W), matAct G₀ ((W + W.transpose).adjugate * W.transpose),
    matAct_hom G₀ _, matAct_hom G₀ _, ?_, ?_, ?_⟩
  · rw [← matAct_one G₀, ← h2]
    refine eighthPowerGroupObj_hom_ext G₀ fun i => ?_
    rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
  · have hC : (cubeLB (powObj G₀ 8) ![𝟙 (powObj G₀ 8), matAct G₀ ((W + W.transpose).adjugate * W)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hE hC).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC, lam_cls_e8LB hL hΘ W hE, cls_e8LB hL W hE]
    have e := formPair_act_right hL hΘ (W + W.transpose) ((W + W.transpose).adjugate * W)
      (𝟙 (powObj G₀ 8)) (𝟙 (powObj G₀ 8))
    rw [Category.id_comp, h1] at e
    exact e.symm
  · have hC1 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W),
        snd (powObj G₀ 8) (powObj G₀ 8)] (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    have hC2 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8),
        snd (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W.transpose)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hC1 hC2).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC1, GlobalTheory.CechPic.cls_cube_two hE _ _ hC2, lam_cls_e8LB hL hΘ W hE,
      lam_cls_e8LB hL hΘ W hE, formPair_act_left hL hΘ, formPair_act_right hL hΘ, h3]

end GlobalTheory.PowE8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatementStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.EigenvalueStatement : EigSt := by
  first | exact @GlobalTheory.EigDiff.eigSt_holds | exact GlobalTheory.EigDiff.eigSt_holds | (intros; apply GlobalTheory.EigDiff.eigSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinRuleOfQExpansionStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_rule_of_q_expansion : GlobalTheory.RealMult.QExpansionOnAll → EisExp → EisMod → EisFourier → TorusForm → EisRule := by
  first | exact @GlobalTheory.EisRuleProof.eisRule_of | exact GlobalTheory.EisRuleProof.eisRule_of | (intros; apply GlobalTheory.EisRuleProof.eisRule_of <;> assumption)
end

