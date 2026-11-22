import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLift
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem root_congr {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} {t t' : T ⟶ S} (e : t = t')
    (h : Root A P t) : Root A P t' := e ▸ h

theorem residue_lift (R R' k'' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Field k''] [Algebra (ResidueField R) k'']
    (ε : ResidueField R ⊗[R] R' ≃ₐ[ResidueField R] k'') :
    ∃ φ : k'' →+* ResidueField R', φ.comp (algebraMap (ResidueField R) k'') =
      algebraMap (ResidueField R) (ResidueField R') := by
  let g₂ : ResidueField R ⊗[R] R' →ₐ[ResidueField R] ResidueField R' :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  refine ⟨(g₂.comp ε.symm.toAlgHom).toRingHom, ?_⟩
  ext a
  exact (g₂.comp ε.symm.toAlgHom).commutes a

theorem exists_rigLB_sFam :
    ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.FormallyUnramified ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro o _ ζ g n F R _ _ _ hR y
  haveI : IsAdicComplete (maximalIdeal R) R := hR
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have hAb := F.univ.ab
  have hP := F.univ.isLB
  let k := ResidueField R
  let t₀ : Sp k ⟶ F.X := spMap (residue R) ≫ y

  have h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀) :=
    root_geom F (AlgebraicClosure k) _

  obtain ⟨B, hB, h₂⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁
  haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩
  haveI : Module.Finite k B := Algebra.IsIntegral.finite

  obtain ⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩ := GlobalTheory.T.exists_complete_local_geomDomain' k B inferInstance
  let tC : Sp C ⟶ F.X := spMap (algebraMap k C) ≫ t₀
  have h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC) := by
    refine root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))
    simp only [tC, ← Category.assoc, spMap_comp']
    congr 2
    exact ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))
  have h₄ : Root F.univ.A F.univ.P tC :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃

  obtain ⟨B', hB', h₅⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ C h₄
  have hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B') := by
    intro K _ _ h1 h2
    haveI := hdom K h1 h2
    let m : K ⊗[k] B' →ₐ[K] K ⊗[k] C := Algebra.TensorProduct.map (AlgHom.id K K) B'.val
    have hm : Function.Injective m := by
      have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap)
        Subtype.val_injective
      exact this
    exact hm.isDomain m
  obtain ⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩ := GlobalTheory.T.exists_separable_point_of_geometrically_domain k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'
  have h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀) := by
    refine root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact ψ.comp_algebraMap

  haveI : Module.Finite (ResidueField R) k'' := hfin
  haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep
  obtain ⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R k''
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := Algebra.FormallyUnramified.map_maximalIdeal
  have hcR' : IsAdicComplete (maximalIdeal R') R' := by
    have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this
  haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance
  let ρ : R →+* R' := algebraMap R R'
  obtain ⟨φ, hφ⟩ := residue_lift R R' k'' ε
  let T : Sp R' ⟶ F.X := spMap ρ ≫ y
  have h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T) := by
    refine root_congr ?_ (h₆.comp hAb (spMap φ))
    simp only [T, t₀, ← Category.assoc, spMap_comp']
    congr 2
    rw [← RingHom.comp_assoc, hφ]
    exact (ResidueField.map_comp_residue ρ).symm
  obtain ⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩ :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ
  have hP' : (F.univ.P.pull β₂).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _
  have hker := GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2
  obtain ⟨M, hM, ⟨hcub⟩⟩ := exists_rigLB_cubical R' B₁ hB₁ L hL
  have hK := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ
  have hA := GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal F R' T B₁ β β₂ hβ hsq L hL hΛ
  subst hM
  have hinj : Function.Injective ρ := by
    letI : Algebra.Etale R R' := het
    haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective R R'
  exact ⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR,
    RingHom.formallyUnramified_algebraMap.mpr inferInstance, B₁, inferInstance, inferInstance, β, β₂, M, hcub,
    hβ, hsq, hA, hK, hΛ⟩

end GlobalTheory.PolBundleLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasis
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobUnit

theorem isUnit_of_isUnit_map {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) (b : B) (hb : IsUnit (θ b)) : IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b', hb'⟩ := hF.surj (↑u⁻¹ : O)
  have hx0 : θ (b * b' - 1) = 0 := by
    rw [map_sub, map_mul, hb', ← hu, map_one, Units.mul_inv, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hx0
  haveI := hF.complete
  have hj : (p : B) * y ∈ (⊥ : Ideal B).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : B))))
  have hu1 := (Ideal.mem_jacobson_bot.1 hj) (-(-1) ^ p)
  have hgeom := mul_neg_geom_sum (-(b * b' - 1)) p
  have h2 : (1 - -(b * b' - 1)) * ∑ i ∈ Finset.range p, (-(b * b' - 1)) ^ i =
      (p : B) * y * (-(-1) ^ p) + 1 := by
    rw [hgeom, neg_pow, hy]; ring
  have h3 : IsUnit (1 - -(b * b' - 1)) := isUnit_of_mul_isUnit_left (h2 ▸ hu1)
  have h4 : (1 - -(b * b' - 1)) = b * b' := by ring
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left h3

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (a : O) :
    ∃ r : O, r ^ p = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Fact.out : p.Prime).pos
  have h1 : v z ≤ 1 := by
    have := hv.map_le_one a
    rw [← hz, map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).1 this
  obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
  exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩

theorem frob_matrix_isUnit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA U hU
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hm : ∀ x : O, ¬IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal O := fun x =>
    (IsLocalRing.mem_maximalIdeal x).symm
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (hm _).1 (Fact.out)
  have hσ : ∀ b, ∃ z, F.σ b = b ^ p + (p : F.B) * z := fun b => by
    obtain ⟨z, hz⟩ := F.σ_pow b
    exact ⟨z, by rw [← hz]; ring⟩
  have hσm : ∀ b, F.θ b ∈ IsLocalRing.maximalIdeal O → F.θ (F.σ b) ∈ IsLocalRing.maximalIdeal O := by
    intro b hb
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add, map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hb _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ hpm)
  have key : ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) →
      ∀ l, ¬IsUnit (F.θ (w l)) := by
    intro w hw
    have h1 := GlobalTheory.T.quasiLog_first_block_small_of_frobenius p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU w hw
    have h2 := GlobalTheory.T.small_mod_maximal_of_frobenius_image_small p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU (fun j => w (Sum.inr j)) (by
      intro l
      rw [hm]
      have hsplit : U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) (fun j => w (Sum.inr j)) :
          Fin d ⊕ Fin k → F.B) j)) l = U.mulVec (fun j => F.σ (w j)) l -
          ∑ m, U l m * F.σ ((Sum.elim (fun i => w (Sum.inl i)) (fun _ => 0) :
            Fin d ⊕ Fin k → F.B) m) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        cases m <;> simp
      rw [hsplit, map_sub]
      refine Ideal.sub_mem _ ((hm _).1 (hw l)) ?_
      rw [map_sum]
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (hσm _ ?_)
      cases m with
      | inl i => simpa using (hm _).1 (h1 i)
      | inr j => simp)
    intro l
    cases l with
    | inl i => exact h1 i
    | inr j => exact h2 j
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_map F.frame
  rw [RingHom.map_det]
  by_contra hdet
  set M := (U.map F.θ).map (IsLocalRing.residue O) with hMdef
  have hM : M.det = 0 := by
    rw [show M = (IsLocalRing.residue O).mapMatrix (F.θ.mapMatrix U) from rfl, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 hdet)
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hlift : ∀ l, ∃ b : F.B, IsLocalRing.residue O (F.θ b) ^ p = x l := by
    intro l
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x l)
    obtain ⟨r, hr⟩ := exists_pow_eq (p := p) hv a
    obtain ⟨b, hb⟩ := F.frame.surj r
    exact ⟨b, by rw [hb, ← map_pow, hr, ha]⟩
  choose w hw using hlift
  have hres : ∀ b, IsLocalRing.residue O (F.θ (F.σ b)) = IsLocalRing.residue O (F.θ b) ^ p := by
    intro b
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add, map_pow, map_mul, map_natCast, map_add, map_pow, map_mul,
      (IsLocalRing.residue_eq_zero_iff _).2 hpm, zero_mul, add_zero]
  have hk := key w (by
    intro l
    rw [hm, ← IsLocalRing.residue_eq_zero_iff]
    have := congrFun hx l
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.map_apply, Pi.zero_apply] at this ⊢
    rw [map_sum, map_sum]
    simpa [hres, hw] using this)
  apply hx0
  funext l
  rw [← hw l, (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 (hk l)), zero_pow (Fact.out : p.Prime).ne_zero,
    Pi.zero_apply]

end GlobalTheory.FrobUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem isNil_frobenius_chart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU
  set M := U * blk d k (p : F.B) 1 with hM
  let T : (Fin d ⊕ Fin k → F.B) → (Fin d ⊕ Fin k → F.B) := fun w => M.mulVec fun j => F.σ (w j)
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθp : F.θ (p : F.B) = (p : O) := map_natCast _ _
  have nu_iff : ∀ x : O, ¬IsUnit x ↔ v (algebraMap O C x) < 1 := fun x => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩
  have nu_add : ∀ x y : O, ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y) := by
    intro x y hx hy
    rw [nu_iff] at hx hy ⊢
    rw [map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  have nu_sum : ∀ (s : Finset (Fin d ⊕ Fin k)) (f : Fin d ⊕ Fin k → O),
      (∀ i ∈ s, ¬IsUnit (f i)) → ¬IsUnit (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using not_isUnit_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact nu_add _ _ (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have stepA : ∀ w : Fin d ⊕ Fin k → F.B, (∀ j, ¬IsUnit (F.θ (w (Sum.inr j)))) →
      ∀ i, ¬IsUnit (F.θ (T w i)) := by
    intro w hw i
    show ¬IsUnit (F.θ (∑ l, M i l * F.σ (w l)))
    rw [map_sum]
    apply nu_sum
    intro l _
    rw [hM, blk, Matrix.mul_diagonal]
    cases l with
    | inl l =>
      simp only [Sum.elim_inl, map_mul, hθp]
      exact fun h => hp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h))
    | inr j =>
      simp only [Sum.elim_inr, mul_one, map_mul]
      obtain ⟨c', hc'⟩ := F.σ_pow (w (Sum.inr j))
      have hs : F.θ (F.σ (w (Sum.inr j))) = F.θ (w (Sum.inr j)) ^ p + p * F.θ c' := by
        have := congrArg F.θ hc'
        rw [map_sub, map_mul, map_pow, hθp] at this
        linear_combination this
      rw [hs]
      refine fun h => nu_add _ _ ?_ ?_ (isUnit_of_mul_isUnit_right h)
      · exact fun h' => hw j ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).1 h')
      · exact fun h' => hp (isUnit_of_mul_isUnit_left h')
  have hQL : ∀ w : Fin d ⊕ Fin k → F.B, QL μ' ⊤ (comb w e) := fun w => GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination _ _ _ F.θ d μ' hlift _ e hbas.1 w
  have hstep : ∀ w : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb w e) - comb (T w) e) :=
    fun w => GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral p F.B F.Q F.σ F.s F.s_alg d _ e M hU w
  have hlf : ∀ w : Fin d ⊕ Fin k → F.B, ∃ a : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) a = defect μ' p (comb w e) := by
    intro w
    have h := (QLogDefect.main p F.B O F.Q F.θ F.frame d μ' hlift ⊤ _ (hQL w) p).1
    choose b _ hb using h
    refine ⟨(fun α => b α : MvPowerSeries (Fin d) F.B), MvPowerSeries.ext fun α => ?_⟩
    exact (hb α).symm
  choose A hA using hlf
  let δ : (Fin d ⊕ Fin k → F.B) → G.A 1 := fun w => c.ev 1 (map F.θ (A w))
  set I := Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) with hI
  have hδstep : ∀ w : Fin d ⊕ Fin k → F.B, δ (T w) - δ w ^ p ∈ I := fun w =>
    GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow p C v O hv ε hε F G d c μ' hlift hmap _ _ _ _ (hQL w) (hQL (T w)) (hstep w) (hA w) (hA (T w))
  have hδit : ∀ n w, δ (T^[n] w) - δ w ^ (p ^ n) ∈ I := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      have h1 := hδstep (T^[n] w)
      have h2 : δ (T^[n] w) ^ p - (δ w ^ p ^ n) ^ p ∈ I :=
        I.mem_of_dvd (sub_dvd_pow_sub_pow _ _ p) (ih w)
      have := I.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hconst : ∀ w : Fin d ⊕ Fin k → F.B, constantCoeff (map F.θ (A w)) = 0 := by
    intro w
    have h0 := GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect p F.B O F.Q F.θ F.frame d μ' hlift _ (hQL w) p
    rw [← hA w, MvPowerSeries.constantCoeff_map] at h0
    have h2 : constantCoeff (A w) = 0 := F.frame.inj (by rw [h0, map_zero])
    rw [MvPowerSeries.constantCoeff_map, h2, map_zero]
  obtain ⟨N0, hN0⟩ := GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p p O G d c
  have hsmallp : ∀ x : G.A 1, (p : G.A 1) ∣ x → x ∈ I := by
    rintro x ⟨y, rfl⟩
    apply I.mul_mem_right
    apply Ideal.subset_span
    exact ⟨(p : O), hp, map_natCast _ _⟩
  have hδ0 : ∀ w : Fin d ⊕ Fin k → F.B, δ w ^ (p ^ N0) ∈ I := by
    intro w
    apply hsmallp
    have hle : N0 ≤ p ^ N0 := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Dvd.dvd.mul_left (hN0 _ (hconst w)) _
  refine ⟨N0 + 1, fun w i => ?_⟩
  rw [Function.iterate_succ_apply']
  apply stepA
  intro j
  apply GlobalTheory.T.levelOne_defects_independent_mod_maximal p C v O hv ε hε F G d c μ' hlift hmap k e hbas hadp _ (A _) (hA _)
  have := I.add_mem (hδit N0 w) (hδ0 w)
  rwa [sub_add_cancel] at this

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep.DescentBaseChange

theorem unitS_subfield {K : Type} [Field K] (k₀ : Subfield K) (u : k₀ˣ) :
    ZM.unitS (spMap k₀.subtype ≫ spMap (RingHom.id k₀)) u = unitOn (Units.map k₀.subtype.toMonoidHom u) := by
  ext
  simp only [ZM.unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (k₀.subtype.comp (RingHom.id k₀)))
  exact (congrArg (fun f => f.hom (u : k₀)) this).symm

theorem tObj_of_baseChange : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (N : ℕ), (N : K) ≠ 0 → ∀ (J : Type) (b : ZM.TBase k₀ N), ∃ (t : ZM.TObj D.P.g N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀))) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
  intro V₁ _ _ D K _ _ ev k₀ N hN J b
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨P, φ, hφ, hg, hm, w, hw⟩ := L1.polBaseChange _ _ (spMap ev) D.P
  have hpb : IsGrpPullback P.A D.P.A (spMap ev) φ := by
    refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl
  let ze : Kˣ := Units.map k₀.subtype.toMonoidHom b.ζ
  have hze : IsPrimitiveRoot ze N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K k₀.subtype)
  obtain ⟨pt, hpt, hpw⟩ := GlobalTheory.EllipticLevel.exists_symplectic_system L1 P N hN ze hze
  have hu := unitS_subfield k₀ b.ζ
  have key : ∀ g', P.g = g' → ∃ (t : ZM.TObj g' N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀)))
      (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
    rintro _ rfl
    exact ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
             ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := hpt
             bij := GlobalTheory.symplectic_system_torsion_basis L1 K P N ze pt hN hze hpt hpw
             pairing := hu ▸ hpw
             act := fun _ => 𝟙 _, hom := fun _ => inferInstance }, φ, hpb, LBIso.symm ⟨w, hw⟩⟩
  exact key _ hg

theorem tBase_of_isAlgClosed (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharZero k₀] (N : ℕ) (hN : N ≠ 0) : Nonempty (ZM.TBase k₀ N) := by
  haveI : NeZero (N : k₀) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N k₀)
    (Polynomial.degree_cyclotomic_pos N k₀ (Nat.pos_of_ne_zero hN)).ne'
  have hp : IsPrimitiveRoot z N := (Polynomial.isRoot_cyclotomic_iff).1 hz
  exact ⟨⟨(hp.isUnit (Nat.pos_of_ne_zero hN).ne').unit, (Nat.cast_ne_zero.2 hN : (N : k₀) ≠ 0).isUnit,
    fun K _ β => hp.map_of_injective β.injective⟩⟩

theorem polarised_part_model : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  intro g n hn hodd
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points L1 L2 g Empty (fun x => x.elim) 0 n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield g n hn hodd
  refine ⟨max (max j₁ j₂) 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hDg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hu
  have hj1 : j₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hK : ∀ m : ℕ, m ≠ 0 → (m : K) ≠ 0 := fun m hm => by
    rw [← map_natCast ev]; exact ((hunit m hm).map ev).ne_zero
  haveI : CharZero k₀ := charZero_of_inj_zero fun m hm => by
    by_contra h
    exact hK m h (by simpa using congrArg k₀.subtype hm)
  have hN0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  obtain ⟨b⟩ := tBase_of_isAlgClosed k₀ ((n ^ j) ^ 2) hN0
  obtain ⟨t, π₁, hπ, hL⟩ := tObj_of_baseChange V₁ D K ev k₀ ((n ^ j) ^ 2) (hK _ hN0) Empty b
  subst hDg
  obtain ⟨v, hv⟩ := ZM.TObj.exists_hasTh_of_isLocalRing L1 L2 (hodd.pow) t
  have hspan := ZM.FamilyScheme.span_theta L1 L2 t n v hn.two_le (dvd_pow_self n (by omega)) hv
  obtain ⟨a', ha'⟩ : ∃ a', v a' ≠ 0 := by
    by_contra h
    push_neg at h
    have : Set.range v ⊆ {0} := by rintro _ ⟨a, rfl⟩; exact h a
    rw [Ideal.span_eq_bot.2 (fun x hx => this hx)] at hspan
    exact bot_ne_top hspan
  have hr := hj₂ j hj2 V₁ hCN hunit D rfl X C e u mo hmo hT K ev k₀ hk₀ hu k₀ Empty b _ t π₁ hπ hL v hv
  choose r hrk hr using fun a => hr a a' ha'
  let w : ZM.Ix D.P.g ((n ^ j) ^ 2) → k₀ := fun a => ⟨r a, hrk a⟩
  have hw : t.HasTh (𝟙 _) (fun a => k₀.subtype (w a)) :=
    GlobalTheory.GenericObject.hasTh_unit_mul t _ v _ (v a')⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero ha')) (fun a => by
      show r a = (v a')⁻¹ * v a
      rw [hr a, mul_comm (r a), ← _root_.mul_assoc, inv_mul_cancel₀ ha', _root_.one_mul]) hv
  have hd : ZM.VeryDense (ZM.objPrimes b (fun x : Empty => x.elim) 0 (RingHom.id k₀) w) := by
    intro q f hq hf
    have hq0 : q = ⊥ := by
      rcases Ideal.eq_bot_or_top q with h | h
      · exact h
      · exact absurd h hq.ne_top
    subst hq0
    exact ⟨⊥, ⟨K, inferInstance, inferInstance, k₀.subtype, t, (RingHom.injective_iff_ker_eq_bot _).1 k₀.subtype_injective,
      fun x => x.elim, hw⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, -, hmap⟩ := hj₁ j hj1 k₀ b k₀ (RingHom.id k₀) w hd
  obtain ⟨φ, hφ, hφL, -, -⟩ := hmap K k₀.subtype t (fun x => x.elim) hw
  obtain ⟨w', hw'⟩ := LBIso.trans (pull_isLB D.P.isLB π₁) t.isLB (pull_isLB t₀.isLB φ) (LBIso.symm hL) hφL
  exact ⟨t₀.A, inferInstance, t₀.ab.comm, t₀.L, t.A, inferInstance, π₁, φ, w', t₀.ab, t₀.isLB, hπ, hφ, hw'⟩

end GlobalTheory.USep.DescentBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfPrintsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.share_of_toroidal : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share := by
  first | exact @GlobalTheory.CovTop.ShareRowsNef.share | exact GlobalTheory.CovTop.ShareRowsNef.share | (intros; apply GlobalTheory.CovTop.ShareRowsNef.share <;> assumption)
end

