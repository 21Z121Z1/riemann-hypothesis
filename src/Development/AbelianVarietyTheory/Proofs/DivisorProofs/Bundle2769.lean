import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

namespace GlobalTheory.DetHT.TestPt

theorem spm_spm {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] (φ : R →+* S) (ψ : S →+* S') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem exists_chart {X : Scheme.{0}} {K : Type} [Field K] (z : Sp K ⟶ X) :
    ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (φ : R →+* K), IsOpenImmersion ξ ∧ spMap φ ≫ ξ = z := by
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (z q)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hr : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    have : q' = q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU'.fromSpec z hr : Sp K ⟶ Spec Γ(X, U))
  refine ⟨Γ(X, U), inferInstance, hU'.fromSpec, φ.hom, inferInstance, ?_⟩
  have : spMap φ.hom = IsOpenImmersion.lift hU'.fromSpec z hr := hφ
  rw [this]
  exact IsOpenImmersion.lift_fac _ _ _

theorem exists_finite_subfield {R F C : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field F] [CharZero F] [Field C]
    [Algebra F C] {K : Type} [Field K] (k : K →+* C) (hK : ∀ a : K, IsAlgebraic ℤ a) (φ₀ : R →+* K) :
    ∃ L : IntermediateField F C, FiniteDimensional F L ∧ ∀ a, (k.comp φ₀) a ∈ L := by
  have hφ : ∀ a, IsAlgebraic ℤ ((k.comp φ₀) a) := fun a => (hK (φ₀ a)).algHom k.toIntAlgHom
  generalize k.comp φ₀ = φ at hφ ⊢
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  refine ⟨IntermediateField.adjoin F (φ '' (s : Set R)), ?_, fun a => ?_⟩
  · haveI : Finite (φ '' (s : Set R)) := (s.finite_toSet.image φ).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    exact ((hφ a).extendScalars (S := F) (algebraMap ℤ F).injective_int).isIntegral
  · have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B)
    (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

theorem exists_integral_point {A : Type} [CommRing A] [Module.Finite ℤ A] {X : Scheme.{0}} (s : X ⟶ Sp A)
    (hs : IsProper s) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (k : K →+* ℂ_[p]) (hK : ∀ a : K, IsAlgebraic ℤ a)
    (z : Sp K ⟶ X) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO ≫ yT = spMap k ≫ z := by
  obtain ⟨R, _, ξ, φ, hξ, rfl⟩ := exists_chart z
  let f : A →+* R := (Spec.preimage (ξ ≫ s)).hom
  have hf : spMap f = ξ ≫ s := Spec.map_preimage (ξ ≫ s)
  letI : Algebra A R := f.toAlgebra
  haveI : Algebra.FiniteType A R := by
    have h : LocallyOfFiniteType (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let T₀ : CDVR := ⟨ℤ_[p]⟩
  have hT₀ : T₀.FinRes := Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  let g₀ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have hg₀ : ∀ a, g₀ a ∈ 𝓞_ℂ_[p] := fun a => by
    rw [GlobalTheory.CdvrLiftCp.mem_int_iff']
    show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  have hg₀i : Function.Injective g₀ :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  let kO₀ : T₀.V →+* 𝓞_ℂ_[p] := g₀.codRestrict 𝓞_ℂ_[p] hg₀
  let k₀ : T₀.Fr →+* ℂ_[p] := IsFractionRing.lift (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i
  have hk₀ : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO₀ a) = k₀ (algebraMap T₀.V T₀.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i a).symm
  letI : Algebra T₀.Fr ℂ_[p] := k₀.toAlgebra
  haveI : CharZero T₀.Fr := algebraRat.charZero _
  obtain ⟨L, hL, hmem⟩ := exists_finite_subfield (F := T₀.Fr) k hK φ
  let φL : R →+* L := (k.comp φ).codRestrict L hmem
  let kL : L →+* ℂ_[p] := L.val.toRingHom
  have hφL : kL.comp φL = k.comp φ := rfl
  obtain ⟨T', -, -, ψ, kO', hfin, hinj, -, -, hkO', hint⟩ :=
    GlobalTheory.CdvrLiftCp.exists_cdvr_lift p T₀ hT₀ kO₀ k₀ hk₀ L kL (fun a => rfl)
  obtain ⟨β', hβ'⟩ := hint A (φL.comp f) (fun a => by
    rw [← GlobalTheory.CdvrLiftCp.mem_int_iff']
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral 𝓞_ℂ_[p] ((kL.comp (φL.comp f)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom 𝓞_ℂ_[p]) _ (RingHom.ext_int _ _) h1
    exact (PadicComplexInt.integers p).mem_of_integral h2)
  have hring : (ψ.toRingHom.comp φL).comp f = (algebraMap T'.V (FractionRing T'.V)).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  obtain ⟨yT, hyT⟩ := exists_extend s hs (V := T'.V) (spMap (ψ.toRingHom.comp φL) ≫ ξ) (spMap β') (by
    rw [Category.assoc, ← hf, spm_spm, spm_spm, hring])
  refine ⟨T', kO', yT, hfin, hinj, ?_⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' =
      (kL.comp ψ.symm.toRingHom).comp (algebraMap T'.V (FractionRing T'.V)) := RingHom.ext hkO'
  have hid : (kL.comp ψ.symm.toRingHom).comp (ψ.toRingHom.comp φL) = k.comp φ := by
    rw [← hφL]
    ext a
    simp
  rw [← Category.assoc, spm_spm, hrk, ← spm_spm, Category.assoc, ← hyT, ← Category.assoc, spm_spm, hid,
    ← Category.assoc, spm_spm]

end GlobalTheory.DetHT.TestPt

namespace GlobalTheory.DetHT

theorem testPtSt : TestPtSt := by
  intro E _ _ _ H Dw l Xo c Z p _ _ P hP
  obtain ⟨K, _, k, z, hK, hz⟩ := hP
  obtain ⟨T, kO, yT, hT, hkO, h⟩ :=
    TestPt.exists_integral_point Z.s (projProper _ _ _ Z.proj) p k hK (z ≫ Z.j)
  refine ⟨spMap kO ≫ yT, ?_, T, kO, yT, hT, hkO, rfl⟩
  rw [h, hz, Category.assoc]

end GlobalTheory.DetHT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

variable {X H Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem sval_eq_secRatio_mul {φ : K → (H ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ H) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (ha : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (secRatio a b) * sval a r z J := by
  have hc := hJ.mem φ r
  have hm : r z ∈ nonzeroLocus a ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨ha, hc⟩
  have e := congrArg (gs r z _) (secRatio_spec a b (fun k => J (r ≫ φ k)))
  rw [gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

theorem pullRatio_ι_comp {R : Type} [CommRing R] {M : ℕ} (P : H ⟶ PSpace R M) {U : H.Opens} {i : Fin (M + 1)}
    (hi : U ≤ P ⁻¹ᵁ chart R M i) (r : Z ⟶ H) (W : Z.Opens) (hW : W ≤ r ⁻¹ᵁ U)
    (h : ⊤ ≤ (W.ι ≫ r ≫ P) ⁻¹ᵁ chart R M i) (j : Fin (M + 1)) :
    pullRatio (W.ι ≫ r ≫ P) ⊤ i h j =
      (W.ι.appLE (r ⁻¹ᵁ U) ⊤ (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW))).hom
        ((r.app U).hom (pullRatio P U i hi j)) := by
  have hW' : ⊤ ≤ W.ι ⁻¹ᵁ (r ⁻¹ᵁ U) := W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW)
  rw [pullRatio_of_eq (Category.assoc W.ι r P).symm h ((hW'.trans ((W.ι ≫ r).preimage_mono hi))),
    ← appLE_pullRatio (W.ι ≫ r) hW', Scheme.Hom.app_eq_appLE, appLE_appLE]

end GlobalTheory.Mum.ThetaSep

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

theorem agree_near_of_minors : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ)
    (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤),
    IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J =
      sval (τ l) y.left z J * sval (τ j) y'.left z J) →
    ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  intro R _ _ D Y k N τ hτ hImm T y y' z J hJ hrel
  have hmono : Mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := inferInstance
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y.left z)))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y'.left z)))
  have ua : IsUnit (sval (τ j₀) y.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hj₀
  have ubi : IsUnit (sval (τ i) y'.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hi
  have ub : IsUnit (sval (τ j₀) y'.left z J) := by
    have h := hrel j₀ i
    have : IsUnit (sval (τ i) y.left z J * sval (τ j₀) y'.left z J) := h ▸ ua.mul ubi
    exact isUnit_of_mul_isUnit_right this
  have hj₀' : y'.left z ∈ nonzeroLocus (τ j₀) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).2 ub
  have hg : ∀ j, gs y.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) =
      gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) := by
    intro j
    have h := hrel j₀ j
    rw [sval_eq_secRatio_mul (τ j₀) (τ j) y.left z hJ hj₀,
      sval_eq_secRatio_mul (τ j₀) (τ j) y'.left z hJ hj₀'] at h
    refine ((ua.mul ub).mul_right_cancel ?_).symm
    calc _ = sval (τ j₀) y.left z J * (gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) *
          sval (τ j₀) y'.left z J) := by ring
      _ = _ := by rw [h]; ring
  have hW : ∀ j, ∃ W : T.left.Opens, z ∈ W ∧ ∃ (h₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀))
      (h₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀)),
      resG T.left h₁ ((y.left.app _).hom (secRatio (τ j₀) (τ j))) =
        resG T.left h₂ ((y'.left.app _).hom (secRatio (τ j₀) (τ j))) := by
    intro j
    have e := hg j
    rw [gs_eq _ z _ hj₀, gs_eq _ z _ hj₀'] at e
    obtain ⟨W, hzW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq T.left.presheaf z hj₀ hj₀' _ _ e
    exact ⟨W, hzW, leOfHom iU, leOfHom iV, e'⟩
  choose Wj hzWj h₁ h₂ heq using hW
  let W : T.left.Opens := Finset.univ.inf Wj
  have hzW : z ∈ W := Finset.inf_induction (p := fun U : T.left.Opens => z ∈ U) trivial
    (fun _ h _ h' => ⟨h, h'⟩) (fun j _ => hzWj j)
  have hWle : ∀ j, W ≤ Wj j := fun j => Finset.inf_le (Finset.mem_univ j)
  refine ⟨W, hzW, (cancel_mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ)).1 ?_⟩
  have hpre := toProj_preimage_chart Y.H.hom τ hτ j₀
  have hA : ∀ (r : T.left ⟶ Y.H.left), W ≤ r ⁻¹ᵁ nonzeroLocus (τ j₀) →
      ⊤ ≤ (W.ι ≫ r ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) ⁻¹ᵁ chart R N j₀ := fun r hr =>
    (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hr)).trans
      ((W.ι ≫ r).preimage_mono hpre.ge)
  have hy₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₁ j₀)
  have hy₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₂ j₀)
  simp only [Category.assoc]
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, j₀, hA _ hy₁, hA _ hy₂, fun j => ?_⟩
  · simp only [Category.assoc, toProj_str]
    rw [Over.w y, Over.w y']
  · rw [pullRatio_ι_comp _ hpre.ge _ W hy₁, pullRatio_ι_comp _ hpre.ge _ W hy₂, pullRatio_toProj]
    have hW₁ : ⊤ ≤ W.ι ⁻¹ᵁ Wj j := W.ι_preimage_self.ge.trans (W.ι.preimage_mono (hWle j))
    rw [← appLE_resG W.ι (h₁ j) hW₁, ← appLE_resG W.ι (h₂ j) hW₁, heq j]

end GlobalTheory.Mum.ThetaSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.CoordNe

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem perp_top (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem TT_eq_bot {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {z : M.Z} (hz : z ∈ U₀) :
    S.TT M z = ⊥ := by
  have h : S.supI M z = {x | S.th x ≠ 0} := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => ?_⟩⟩
    rw [div_eq_mul_inv]
    exact RatModel.ringOn_le_O hz (mul_mem (hO.le (S.th_mem i)) (hO.th_unit x hx))
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, S.supp, perp_top]

theorem isOpen_TT (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

theorem coord_ne_zero : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm hO x R _ _ _ j D hPsi p _ y ev hCen hfac α s hs h0
  let w : Sp (PadicAlgCl p) := (⊥ : PrimeSpectrum (PadicAlgCl p))
  have hW : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
    refine IsOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous ?_
    rw [FinalForm.ab]
    exact isOpen_TT S M
  have hp : spMap ev (gPt p w) ∈ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfac, FinalForm.ab]
    exact TT_eq_bot hO (hCen.2 ⟨w, rfl⟩)
  apply GlobalTheory.PsiCoordLocal.not_mem_of_coord hW hp (hPsi α) hs
  change (ev s : PadicAlgCl p) ∈ (⊥ : Ideal (PadicAlgCl p))
  exact h0

end GlobalTheory.Poinc.CoordNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPer

theorem prod_psum_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {U : Type} [CommGroup U]
    (H : ((G ⊗ G).left ⟶ G.left) → U) :
    ∏ K : ULift.{0} (Finset (Fin 2)), H (psum G (x2 G) K.down).left ^ ((-1 : ℤ) ^ (2 - K.down.card)) =
      H (psum G (x2 G) {0, 1}).left * (H (psum G (x2 G) {0}).left)⁻¹ * (H (psum G (x2 G) {1}).left)⁻¹ *
        H (psum G (x2 G) ∅).left := by
  refine (Fintype.prod_equiv Equiv.ulift _
    (fun I => H (psum G (x2 G) I).left ^ ((-1 : ℤ) ^ (2 - I.card))) fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q₂ : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₂, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem periods_alg {U : Type} [CommGroup U] {X : Type} [AddCommGroup X] {P : Type} [Mul P] (c : X → P)
    (c_add : ∀ x y, c (x + y) = c x * c y) (t : X → X → U) (θ : P → P → P → U) (symm : ∀ x y, t x y = t y x)
    (add : ∀ x x' y, t (x + x') y * θ (c x) (c x') (c y) = t x y * t x' y) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → X) :
    (∏ i, ∏ j, t (a i + b i) (a j + b j) ^ W i j) * (∏ i, ∏ j, t (a i) (a j) ^ W i j)⁻¹ *
        (∏ i, ∏ j, t (b i) (b j) ^ W i j)⁻¹ =
      (∏ i, ∏ j, (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j)) * ∏ i, ∏ j, t (a i) (b j) ^ ((W + W.transpose) i j) := by
  have base : ∀ x x' y y' : X, t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ =
      (θ (c x) (c x') (c y * c y') * θ (c y) (c y') (c x) * θ (c y) (c y') (c x'))⁻¹ * (t x y' * t y x') := by
    intro x x' y y'
    have e₁ := add x x' (y + y')
    have e₂ := add y y' x
    have e₃ := add y y' x'
    rw [c_add] at e₁
    have s₁ := symm x (y + y')
    have s₂ := symm x' (y + y')
    have s₃ := symm y x
    have s₄ := symm y' x
    have s₅ := symm y' x'
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃
    have b₁ := E s₁; have b₂ := E s₂; have b₃ := E s₃; have b₄ := E s₄; have b₅ := E s₅
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ b₃ b₄ b₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ + a₃ + b₁ + b₂ + b₃ + b₄ + b₅
  have hij : ∀ i j, t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ * (t (b i) (b j) ^ W i j)⁻¹ =
      (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j) * (t (a i) (b j) ^ W i j * t (a j) (b i) ^ W i j) := by
    intro i j
    rw [← inv_zpow, ← inv_zpow, ← mul_zpow, ← mul_zpow, base, zpow_neg, ← inv_zpow, ← mul_zpow, mul_zpow]
  have hc : ∏ i, ∏ j, t (a j) (b i) ^ W i j = ∏ i, ∏ j, t (a i) (b j) ^ W j i := Finset.prod_comm
  calc _ = ∏ i, ∏ j, (t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ *
        (t (b i) (b j) ^ W i j)⁻¹) := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = _ := Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hij i j
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Matrix.add_apply, Matrix.transpose_apply, zpow_add]
      rw [hc]

end GlobalTheory.Mum.TensPer

namespace GlobalTheory.Mum.TensPer
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem groupSchemePartialSum_twoPoints_empty : psum G (x2 G) ∅ = 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_first : psum G (x2 G) {0} = fst G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_second : psum G (x2 G) {1} = snd G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_both : psum G (x2 G) {0, 1} = fst G G * (snd G G * 1) := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] by decide]
  rfl

end GlobalTheory.Mum.TensPer

open GlobalTheory.Mum.TensPer in

theorem GlobalTheory.Mum.Tens.tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : D.toPre.X, val (D.toPre.tau (x + x') y) (𝟙 _) z J *
      cubV D.toPre.cub z J (cP D.toPre (TK R) x) (cP D.toPre (TK R) x') (cP D.toPre (TK R) y) =
      val (D.toPre.tau x y) (𝟙 _) z J * val (D.toPre.tau x' y) (𝟙 _) z J :=
    fun x x' y => GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ D.tau_bimult x x' y
  have hsym : ∀ x y : D.toPre.X, val (D.toPre.tau x y) (𝟙 _) z J = val (D.toPre.tau y x) (𝟙 _) z J :=
    fun x y => GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ x y
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (T.w.s (fun k => J (D'.toPre.xK y ≫ tensφ T.pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (T.w.s j) = gm m' z _ (T.w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, T.c_pr]; rfl
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, T.c_pr]; rfl
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, T.psi (a + b) z J J' hJ hJ', T.psi a z J J' hJ hJ', T.psi b z J J' hJ hJ', T.psi 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (D.toPre.tau (T.xe 0 i) (T.xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show T.xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (twist_vector_at_zero D J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (D.toPre.tau (T.xe (a + b) i) (T.xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe a i + T.xe b i) (T.xe a j + T.xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cP D.toPre (TK R)) (cPoint_add D.toPre (TK R))
    (fun x y => val (D.toPre.tau x y) (𝟙 _) z J) (cubV D.toPre.cub z J) hsym hadd W (T.xe a) (T.xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningOpenImmersionPullbackSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_open_immersion_pullback_square : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (C' : Type) [CommRing C'] [Algebra R' C'] (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → ∀ (e : ℕ), ∃ (je : Sp (C' ⧸ (I ^ (e + 1)).map (algebraMap R' C')) ⟶ (thickObj R' I e G').left) (_ : IsOpenImmersion je), je.opensRange = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ j.opensRange ∧ IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (pullback.fst G'.hom (thick R' I e)) j ∧ je ≫ (thickObj R' I e G').hom = spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) := by
  first | exact @GlobalTheory.Mum.ThickChart.thick_chart | exact GlobalTheory.Mum.ThickChart.thick_chart | (intros; apply GlobalTheory.Mum.ThickChart.thick_chart <;> assumption)
end

