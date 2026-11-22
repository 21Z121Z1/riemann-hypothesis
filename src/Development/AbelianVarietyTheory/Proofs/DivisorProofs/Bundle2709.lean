import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfPt

theorem exists_spec_of_finite_surjective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsFinite f] [Surjective f] :
    ∃ (C : Type) (_ : CommRing C) (φ : R →+* C) (g : Sp C ⟶ X),
      Function.Injective φ ∧ φ.Finite ∧ g ≫ f = spMap φ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩
  · have hs : Surjective (Spec.map ψ) := by rw [hψ]; infer_instance
    have hd : DenseRange (PrimeSpectrum.comap ψ.hom) := hs.1.denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero] at hd
    rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using hd hx
  · have hf : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (IsFinite.SpecMap_iff ψ).1 hf
  · exact hψ.symm

end GlobalTheory.HalfPt

namespace GlobalTheory.HalfPt

theorem exists_half_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  intro R _ _ _ B _ _ a hCN hAb
  haveI : IsNoetherianRing R := hCN.1
  obtain ⟨hfin, -⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme (Sp R) B hAb 2 (by norm_num)
  have hsurj := GlobalTheory.T.semiAbelian_mul_nat_surjective (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero
  let m : B.left ⟶ B.left := ((𝟙 B) ^ 2 : B ⟶ B).left
  let s : Sp R ⟶ B.left := a.left
  haveI : IsFinite m := hfin
  haveI : Surjective m := hsurj
  haveI : IsFinite (pullback.snd m s) := inferInstance
  haveI : Surjective (pullback.snd m s) := inferInstance
  obtain ⟨C, _, φ, g, hinj, hφf, hg⟩ := exists_spec_of_finite_surjective (pullback.snd m s)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩ := GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R C φ hCN hinj hφf
  have hsB : s ≫ B.hom = 𝟙 (Sp R) := Over.w a
  have hmB : m ≫ B.hom = B.hom := Over.w ((𝟙 B) ^ 2 : B ⟶ B)
  have hfst : pullback.fst m s ≫ B.hom = pullback.snd m s := by
    rw [← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]
  have hρ : spMap σ ≫ spMap φ = spMap ρ := by
    rw [← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let c : Over.mk (spMap ρ) ⟶ B :=
    Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hfst, hg, hρ])
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩
  have hc : c ^ 2 = c ≫ (𝟙 B) ^ 2 := by rw [comp_pow, Category.comp_id]
  rw [hc]
  ext
  simp only [c, Over.comp_left, Over.homMk_left, Category.assoc]
  show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _
  rw [pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]
  rfl

end GlobalTheory.HalfPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

namespace GlobalTheory.ResZeroDepth

theorem exists_harmA_nuLocOf_nonpos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro a n ha hn
  classical
  have hcard : Fintype.card (Lt1 Dw) ≤ n := by
    refine le_trans ?_ hn
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f _ => by unfold rk; omega
  have hdom : Formalism.L2.Pj.DomW Dw a := fun τ i j hij => ha τ hij
  have hinj : Function.Injective (Formalism.L2.Pj.colP Dw hcard) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hcard h)
  refine ⟨MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i)),
    Formalism.L2.Pj.Crude.Pmin_mem Dw.mult n c.F _ _ _ _ _ (fun τ _ => Formalism.L2.Pj.conj_ne_self_of_CM τ) hinj hdom, ?_⟩
  intro T io y C hres e k _
  letI := io.toAlgebra
  have hmap : MvPolynomial.map io (MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i))) =
      Formalism.L2.Pj.P1 Dw T a hcard := by
    rw [MvPolynomial.map_map, RingHom.ext_int (io.comp _) (Int.castRingHom T.Fr)]
    rfl
  obtain ⟨-, f, hf, -, hv⟩ := Formalism.L2.Pj.crude_val C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec
    (Formalism.L2.Pj.satDir_of Formalism.L2.Pj.chart_saturated C) a n hdom hcard
  rw [hmap]
  refine le_trans (iInf_le_of_le f (iInf_le_of_le hf (le_of_eq (congrArg (Formalism.L2.Pj.nval T.V e) hv)))) ?_
  set N := Formalism.L2.Pj.fact1 Dw a hcard with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; unfold Formalism.L2.Pj.fact1
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hu : IsUnit ((N : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hN0
  have hne : ((N : ℕ) : T.Fr) ≠ 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  have hv0 : Formalism.L2.Pj.vV T.V ((N : ℕ) : T.Fr) = 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact GlobalTheory.RefSum.GlobalPoly.vV_of_isUnit T hu
  rw [Formalism.L2.Pj.nval_of_ne hne, hv0]
  simp

end GlobalTheory.ResZeroDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem PullB.vanMod {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b' : D'.SecB k x} (H : PullB hD x b b') {I : Ideal R} {I' : Ideal R'} (hI : I ≤ I'.comap φ) {e : ℕ}
    (hb : VanMod I b e) : VanMod I' b' e := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ :=
    (pull_grp hD).1.w
  have hc := ExpGTrans.famφB_pull hD x
  unfold PullB at H
  have ht : thick R' I' e ≫ specOf φ =
      spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle) ≫ thick R I e := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  obtain ⟨h, hh⟩ : ∃ h : pullback D'.P.A.hom (thick R' I' e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D'.P.A.hom (thick R' I' e) ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) :=
    ⟨pullback.lift _ (pullback.snd D'.P.A.hom (thick R' I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]),
      pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (D'.famφB x κ (pullback.fst D'.P.A.hom (thick R' I' e) y)))
  have e₁ := H _ (pullback.fst D'.P.A.hom (thick R' I' e)) y p q hp (Set.mem_iInter.1 hy)
  have hm : pullback.fst D.P.A.hom (thick R I e) (h y) ∈ LB.wchart D.P.L (D.famφB (hD.xe x)) p :=
    Set.mem_iInter.2 fun κ => by
      have a : h ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.famφB (hD.xe x) κ =
          pullback.fst D'.P.A.hom (thick R' I' e) ≫ D'.famφB x κ ≫
            hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := by
        rw [← Category.assoc, hh, Category.assoc, ← hc κ]
      exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) a).mpr (hp κ)
  have z₀ : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), f y ∈ U → gs f y U 0 = 0 := fun f y U h => by
    rw [gs_eq f y U h, map_zero, map_zero]
  rw [← hh] at e₁
  have e₂ := (Units.mul_right_eq_zero _).1 (e₁.symm.trans ((gs_pull h _ y _ hm _).symm.trans
    ((congrArg (gs h y _) (hb p)).trans (z₀ h y _ hm))))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (z₀ _ y _ hy).symm

theorem exists_intFam_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre), Function.Injective φ → IsLocalHom φ → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k), ∃ F' : IntFam (maximalIdeal W) D'.toPre k, ∀ x, PullB hD x (F.f (hD.xe x)) (F'.f x) := by
  intro R _ _ _ _ D W _ _ _ φ D' hD _ hl k F
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (F.f (hD.xe x))).exists
  have s₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have s₂ : scal (DegPre.BF D'.toPre (FractionRing W)).hom 1 = 1 := by rw [scal, map_one, map_one]
  obtain ⟨E, hE⟩ := exists_fam_of_isPullDeg GlobalTheory.allSixLaws.1.globalFns R W φ D.toPre D'.toPre hD k F.F F.f f'
    (fun α => s₁ ▸ F.ext α) hf'
  have hI : maximalIdeal R ≤ (maximalIdeal W).comap φ := fun a ha => map_nonunit φ a ha
  refine ⟨{ F := E, f := f', ext := fun α => s₂.symm ▸ hE α, small := fun e => ?_ }, hf'⟩
  exact ((F.small e).preimage hD.xe.injective.injOn).subset fun x hx hv => hx (PullB.vanMod (hf' x) hI hv)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivialStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  first | exact @GlobalTheory.PtExt.exists_isChoice | exact GlobalTheory.PtExt.exists_isChoice | (intros; apply GlobalTheory.PtExt.exists_isChoice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtendStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V), IsLocalHom ψ → ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V, IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  first | exact @GlobalTheory.exists_isLocalHom_adicCompletion_extend | exact GlobalTheory.exists_isLocalHom_adicCompletion_extend | (intros; apply GlobalTheory.exists_isLocalHom_adicCompletion_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCancelTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ ψ : PsiOn D' (specOf φ ⁻¹ᵁ hD.W), ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val (ψ.psi x) r z J' := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val a r z J' := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
    swap
    · have v := DegPull.pmaps_val (fun _ => hψ) H r z hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one] at v
      exact v
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc hv using key
  exact ⟨⟨a, ha, hc⟩, hv⟩

end GlobalTheory.PullDegCancelTop

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem trF_sum_elim {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    (φ₁ : K → (Y ⟶ X)) (φ₂ : K' → (Y ⟶ X)) (ε₁ : K → ℤ) (ε₂ : K' → ℤ) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (q q' : K' → L.ι) :
    trF (Sum.elim φ₁ φ₂) (Sum.elim ε₁ ε₂) r z (Sum.elim p q) (Sum.elim p' q') =
      trF φ₁ ε₁ r z p p' * trF φ₂ ε₂ r z q q' := by
  rw [trF, trF, trF, Fintype.prod_sum_type]; rfl

theorem trF_self' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (hp : r z ∈ LB.wchart L φ p) :
    trF φ ε r z p p = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hp k), _root_.one_zpow]

theorem iso_linComb_pull_glue : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  intro X X' Y M hM L' hL' K K' _ _ φ ε ψ e F w₁ hw₁ u hu

  have memE : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (p : K → M.ι) (q : K' → M.ι),
      F (f z) ∈ LB.wchart M φ p → f z ∈ LB.wchart M ψ q →
      f z ∈ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := by
    intro Z f z p q hp hq
    refine Set.mem_iInter.2 fun k => ?_
    cases k with
    | inl k => exact Set.mem_iInter.1 hp k
    | inr i => exact Set.mem_iInter.1 hq i

  have key : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j' : L'.ι) (q : K' → M.ι) (p p' : K → M.ι),
      F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q → F (f z) ∈ LB.wchart M φ p → F (f z) ∈ LB.wchart M φ p' →
      gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ =
        gm f z _ (u.s (Sum.elim p' q)) * (gm (f ≫ F) z _ (w₁.s (p', j')))⁻¹ := by
    intro Z f z j' q p p' hj hq hp hp'
    have a := gen_trans hu f z (memE f z p q hp hq) (memE f z p' q hp' hq)
    rw [trF_sum_elim, trF_self' hM ψ _ f z q hq, _root_.mul_one] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p' j' j' hp hp' hj hj
    have c : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p') = trF (fun k => F ≫ φ k) ε f z p p' := by
      refine (gm_linComb M φ ε (f ≫ F) z p p' hp hp').trans ?_
      simp only [trF, Category.assoc]
    rw [c, gm_self hL' (f ≫ F) z hj, inv_one, _root_.mul_one] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q)) (u.s (Sum.elim p q)) * (gv w₁ (f ≫ F) z p j')⁻¹ =
      gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p' q)) (u.s (Sum.elim p' q)) * (gv w₁ (f ≫ F) z p' j')⁻¹
    rw [a, b]
    generalize trF (fun k => F ≫ φ k) ε f z p p' = T
    generalize gm f z _ (u.s (Sum.elim p' q)) = U
    generalize gv w₁ (f ≫ F) z p' j' = V
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (j' : L'.ι) (q : K' → M.ι),
      ∃ s : Γ(X, (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q →
        F (f z) ∈ LB.wchart M φ p →
        gm f z _ s = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ := by
    intro j' q
    obtain ⟨W, hW⟩ : ∃ W : (K → M.ι) → X.Opens, ∀ p x, x ∈ W p ↔
        F x ∈ L'.U j' ∧ x ∈ LB.wchart M ψ q ∧ F x ∈ LB.wchart M φ p :=
      ⟨fun p => F ⁻¹ᵁ L'.U j' ⊓ (LB.wchart M ψ q ⊓ F ⁻¹ᵁ LB.wchart M φ p), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ p, W p ≤ (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q := fun p x hx =>
      ⟨mem_pull.2 ((hW p x).1 hx).1, ((hW p x).1 hx).2.1⟩
    have l₁ : ∀ p, W p ≤ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := fun p x hx =>
      memE (𝟙 X) x p q ((hW p x).1 hx).2.2 ((hW p x).1 hx).2.1
    have l₂ : ∀ p, W p ≤ F ⁻¹ᵁ (LB.wchart M φ p ⊓ L'.U j') := fun p x hx =>
      ⟨((hW p x).1 hx).2.2, ((hW p x).1 hx).1⟩
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X, W p)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), f z ∈ W p →
        gm f z (W p) (v p) = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ :=
      ⟨fun p => res (l₁ p) (u.s (Sum.elim p q)) * (res (l₂ p) (pullU F _ (w₁.s (p, j'))))⁻¹,
        fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₁ p) hz _)
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₂ p) hz _).trans (gm_pull f F z _ (l₂ p hz) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose p hp using fun k => exists_chart hM (φ k (F x))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, (hW p x).2 ⟨mem_pull.1 hx.1, hx.2, Set.mem_iInter.2 hp⟩⟩) v (fun p p' x hx => by
        have h₁ := (hW p x).1 hx.1
        have h₂ := (hW p' x).1 hx.2
        exact (hv _ (𝟙 X) x p hx.1).trans ((key (𝟙 X) x j' q p p' h₁.1 h₁.2.1 h₁.2.2 h₂.2.2).trans
          (hv _ (𝟙 X) x p' hx.2).symm))
    refine ⟨s, fun Z f z p hj hq hp => ?_⟩
    have hz := (hW p (f z)).2 ⟨hj, hq, hp⟩
    exact (gm_res f z (l₀ p) hz s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hv Z f z p hz))
  choose s hs using glue
  refine ⟨⟨fun P => s (P.1 PUnit.unit) P.2⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z f z j j' (k : K' → M.ι) (k' : K' → M.ι) hj hj' hk hk'
    choose p hp using fun a => exists_chart hM (φ a (F (f z)))
    have hpm : F (f z) ∈ LB.wchart M φ p := Set.mem_iInter.2 hp
    show gm f z _ (s j k) = gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      gm f z _ (s j' k')
    rw [hs j k Z f z p hj hk hpm, hs j' k' Z f z p hj' hk' hpm]
    have a := gen_trans hu f z (memE f z p k hpm hk) (memE f z p k' hpm hk')
    rw [trF_sum_elim, trF_self' hM (fun a => F ≫ φ a) ε f z p (Set.mem_iInter.2 fun a => Set.mem_iInter.1 hpm a), _root_.one_mul] at a
    have c : gm f z _ ((LB.LinComb M ψ e).g k k') = trF ψ e f z k k' := gm_linComb M ψ e f z k k' hk hk'
    have d : trF ψ (fun i => - e i) f z k k' = (trF ψ e f z k k')⁻¹ := by
      simp only [trF, zpow_neg, Finset.prod_inv_distrib]
    rw [d] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p j j' hpm hpm hj hj'
    have c' : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p) = 1 :=
      (gm_linComb M φ ε (f ≫ F) z p p hpm hpm).trans (trF_self' hM φ ε (f ≫ F) z p hpm)
    rw [c', _root_.one_mul] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k)) (u.s (Sum.elim p k)) * (gv w₁ (f ≫ F) z p j)⁻¹ =
      gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      (gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k')) (u.s (Sum.elim p k')) * (gv w₁ (f ≫ F) z p j')⁻¹)
    rw [a, b, c]
    generalize trF ψ e f z k k' = T
    generalize gm f z _ (u.s (Sum.elim p k')) = U
    generalize gv w₁ (f ≫ F) z p j' = V
    generalize gm (f ≫ F) z _ (L'.g j j') = G
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro Z f z J hJ j' hj
    have hp : F (f z) ∈ LB.wchart M φ (fun k => J ((f ≫ F) ≫ φ k)) :=
      Set.mem_iInter.2 fun k => hJ ((f ≫ F) ≫ φ k)
    show gm f z _ (s j' (fun i => J (f ≫ ψ i))) = _
    rw [hs j' _ Z f z _ hj (hJ.mem ψ f) hp,
      val_of u f z J (Sum.elim (fun k => J ((f ≫ F) ≫ φ k)) (fun i => J (f ≫ ψ i)))
        (by rintro (k | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.assoc])]
    exact mul_comm _ _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPowEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_pow_eq' : ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) (m g : ℕ) (hg : Q.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level Q (m ^ 2) ze) (z : baseOver (Sp K) ⟶ Q.A), 0 < m → z ^ m = 1 → ∃ a : Fin (2 * g) → ZMod (m ^ 2), GlobalTheory.levelPoint lev hg a ^ m = z := by
  first | exact @GlobalTheory.exists_levelPoint_pow_eq | exact GlobalTheory.exists_levelPoint_pow_eq | (intros; apply GlobalTheory.exists_levelPoint_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSystemDefectCocycleGlobalFormsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_liftSystemDefect_cocycle_globalForms : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  first | exact @GlobalTheory.LiftSys.exists_defect_cocycle | exact GlobalTheory.LiftSys.exists_defect_cocycle | (intros; apply GlobalTheory.LiftSys.exists_defect_cocycle <;> assumption)
end

