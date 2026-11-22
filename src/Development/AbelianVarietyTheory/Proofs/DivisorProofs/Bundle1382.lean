import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTwConjMemCentMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellMulSimpleUIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertTransferW

theorem complex_smul_left_cancel_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ℂ} {w : V} (hw : w ≠ 0) (h : a • w = b • w) :
    a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem field_smul_left_cancel_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {a b : K} {w : V} (hw : w ≠ 0)
    (h : a • w = b • w) : a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

set_option maxHeartbeats 4000000 in

theorem inertEigenvalues_iff_thetaLift_inertLabels_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hTS hJunk j c c' u u' x x' hx hx' hc hc' hn hn'
  obtain ⟨hcore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hE
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hW0, hWops, -, -, -, -, hWev, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hS hX R.SF hSF j
  obtain ⟨hV, hVops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).2 j A3.A.μ0
  have K : ∀ {cc : Pl D.host.E → List ℤ → ℂ} {z : (A3.A.fam.L j A3.A.μ0).S.Forms},
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ∈ R.Wc' j cc → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ≠ 0 →
      ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cV cW, GlobalTheory.Hk3.MatchW R.toRealDat j A3.A.μ0 P cV cW → ∀ σ : ℂ,
      hV P cV (R.jV j A3.A.μ0 z) = σ • R.jV j A3.A.μ0 z → σ = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW := by
    intro cc z hz hz0 P hP cV cW hM σ hσ
    rw [hWc j cc] at hz
    have h1 := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hcore hS hX R.SF hSF j A3.A.μ0 P hP cV cW hM hV hVops).1 hW0 hWops
      (R.jV j A3.A.μ0 z)
    have h4 := hWev cc P hP cW _ hz
    have h5 : σ • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) :=
      ((R.thG j A3.A.μ0).map_smul σ (R.jV j A3.A.μ0 z)).symm.trans ((congrArg (R.thG j A3.A.μ0) hσ).symm.trans (h1.trans h4))
    exact complex_smul_left_cancel_of_ne_zero hz0 h5
  have hrank : (Vc D j).rank = (A3.A.fam.L j A3.A.μ0).n := R.B.rankL j
  have V1 : ∀ (Q : A3.okI A3.A.μ0) (sq : List ℕ), Formalism.L2.Col.InertTypeOk (Vc D j).rank sq → ∀ f,
      R.jV j A3.A.μ0 (A3.heckeLI j A3.A.μ0 (Q, sq) f) =
        hV (R.plI Q) (Finsupp.single (labIn (Vc D j).rank sq) 1) (R.jV j A3.A.μ0 f) := by
    intro Q sq hsq f
    have tie := (hW.inert.hL j A3.A.μ0).some
    refine ((GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models j A3.A.μ0 _
      (fun k : A3.okI A3.A.μ0 × List ℕ => R.plI k.1) (fun k => labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) ?_ tie (Q, sq) hsq).2.2.2 hV hVops f)
    intro k hk
    obtain ⟨hg, hcj⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI k.1)).1 ⟨k.1, k.1.2, rfl⟩
    refine ⟨hg, hcj, ?_⟩
    exact ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (labIn (Vc D j).rank k.2)).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simp)
  have hx0' : x' ≠ 0 := by rintro rfl; exact hn' (by simp)
  have hopx : ∀ k, A3.heckeLI j A3.A.μ0 k x = u (Sum.inr k) • x := fun k => hx (Sum.inr k)
  have hopx' : ∀ k, A3.heckeLI j A3.A.μ0 k x' = u' (Sum.inr k) • x' := fun k => hx' (Sum.inr k)
  constructor
  · intro hu P d hP hPc hd
    obtain ⟨Q, hQ, rfl⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 P).2 ⟨hP, hPc⟩
    obtain ⟨cV, hM⟩ := ((hTS _ hP hPc).2 j).2 (Finsupp.single d 1)
    obtain ⟨σ, h1, h2⟩ := GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime R.toRealDat hcore.models j A3.A.μ0 hV hVops _ hP hPc
      (fun sq => D.what₂.embLL (u (Sum.inr (⟨Q, hQ⟩, sq)))) (R.jV j A3.A.μ0 x) (R.jV j A3.A.μ0 x')
      (fun sq hsq => ⟨(V1 ⟨Q, hQ⟩ sq hsq x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)),
        (V1 ⟨Q, hQ⟩ sq hsq x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans ((map_smulₛₗ _ _ _).trans
          (congrArg (fun a => D.what₂.embLL a • R.jV j A3.A.μ0 x') (hu _).symm)))⟩) cV
    have e1 := K hc hn _ hP cV _ hM σ h1
    have e2 := K hc' hn' _ hP cV _ hM σ h2
    unfold GlobalTheory.Hk3.evC at e1 e2
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul] at e1 e2
    exact e1.symm.trans e2
  · rintro hcc ⟨⟨Q0, hQ0⟩, sq⟩
    have hPl := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI Q0)).1 ⟨Q0, hQ0, rfl⟩
    rcases hJunk.2 j A3.A.μ0 (⟨Q0, hQ0⟩, sq) with h0 | ⟨y, hy, hop⟩
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) • x = 0 :=
        (hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) • x' = 0 :=
        (hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x').trans (LinearMap.zero_apply x'))
      rw [(smul_eq_zero.mp a1).resolve_right hx0, (smul_eq_zero.mp a2).resolve_right hx0']
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) = u (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0 ((hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x).trans (hopx (⟨Q0, hQ0⟩, y))))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) = u' (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0' ((hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x').trans (hopx' (⟨Q0, hQ0⟩, y))))
      rw [a1, a2]
      rw [← hrank] at hy
      obtain ⟨cW, hM⟩ := ((hTS _ hPl.1 hPl.2).2 j).1 (Finsupp.single (labIn (Vc D j).rank y) 1)
      have b1 := K hc hn _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)))
      have b2 := K hc' hn' _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans (map_smulₛₗ _ _ _)))
      apply D.what₂.embLL.injective
      refine b1.trans (Eq.trans ?_ b2.symm)
      unfold GlobalTheory.Hk3.evC
      refine Finsupp.sum_congr fun d _ => ?_
      split_ifs with hd
      · rw [hcc _ d hPl.1 hPl.2 hd]
      · rfl

end GlobalTheory.InertTransferW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertUniq

section Fixed
variable {L : Type} [Field L]

abbrev fixF (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

abbrev starOfInv (σ : L →+* L) (h : ∀ x, σ (σ x) = x) : StarRing L where
  star := σ
  star_involutive := h
  star_mul x y := by rw [map_mul]; exact mul_comm _ _
  star_add := map_add σ

theorem finrank_fixF (σ : L →+* L) (h : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Module.finrank (fixF σ) L = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx₀)
  have hli : LinearIndependent (fixF σ) ![(1 : L), x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : σ (s : L) = s := s.2
    have ht : σ (t : L) = t := t.2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    change (s : L) + (t : L) * x₀ = 0 at hst
    have h2 : (s : L) + (t : L) * σ x₀ = 0 := by
      have := congrArg σ hst
      rwa [map_add, map_mul, hs, ht, map_zero] at this
    have ht0 : (t : L) = 0 := by
      have : (t : L) * (x₀ - σ x₀) = 0 := by linear_combination hst - h2
      exact (mul_eq_zero.1 this).resolve_right hd
    refine ⟨Subtype.ext ?_, Subtype.ext ht0⟩
    simpa [ht0] using hst
  have hsp : ⊤ ≤ Submodule.span (fixF σ) (Set.range ![(1 : L), x₀]) := by
    intro y _
    set b := (y - σ y) / (x₀ - σ x₀) with hbdef
    have hb : σ b = b := by
      rw [hbdef, map_div₀, map_sub, map_sub, h, h, ← neg_sub y (σ y), ← neg_sub x₀ (σ x₀), neg_div_neg_eq]
    set a := y - b * x₀ with hadef
    have hbm : b * (x₀ - σ x₀) = y - σ y := div_mul_cancel₀ _ hd
    have ha : σ a = a := by
      rw [hadef, map_sub, map_mul, hb]
      linear_combination hbm
    have hy : y = (⟨a, ha⟩ : fixF σ) • (1 : L) + (⟨b, hb⟩ : fixF σ) • x₀ := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change y = a * 1 + b * x₀
      rw [hadef]; ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
  simp

end Fixed

theorem eq_twCent_mul_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  intro E _ _ _ hU n w hs y g hy hbez hyg
  obtain ⟨hc, hinv, hval, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hϖ, -⟩, -⟩ := hns hs
  obtain ⟨-, -, hϖf, hϖv, ⟨x₀, -, hx₀⟩, -⟩ := hϖ
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  letI : StarRing (w.adicCompletion E) := starOfInv (cj w) hinv
  have hle1 : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  have hneq : ∀ x y : w.adicCompletion E, Valued.v x = Valued.v y → ‖x‖ = ‖y‖ := fun x y h =>
    le_antisymm (Valued.toNormedField.norm_le_iff.2 h.le) (Valued.toNormedField.norm_le_iff.2 h.ge)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖi : cj w ϖ⁻¹ = ϖ⁻¹ := by rw [map_inv₀, hϖf]
  have hϖn : 1 < ‖ϖ⁻¹‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, hϖv]
    exact one_lt_inv₀ (by simp) |>.2 (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  letI nF : NontriviallyNormedField (fixF (cj w)) :=
    { (inferInstance : NormedField (fixF (cj w))) with non_trivial := ⟨⟨ϖ⁻¹, hϖi⟩, hϖn⟩ }
  letI : NormedAlgebra (fixF (cj w)) (w.adicCompletion E) :=
    { (inferInstance : Algebra (fixF (cj w)) (w.adicCompletion E)) with
      norm_smul_le := fun r x => by rw [Algebra.smul_def, norm_mul]; exact le_of_eq rfl }
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI hUn : GlobalTheory.JR.Unram (fixF (cj w)) (w.adicCompletion E) :=
    { charZero := ⟨fun a b h => Nat.cast_injective (R := w.adicCompletion E) (by simpa using congrArg (algebraMap (fixF (cj w)) (w.adicCompletion E)) h)⟩
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := (isClosed_eq hc continuous_id).isClosedEmbedding_subtypeVal.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixF (cj w) hinv ⟨x₀, fun h => by rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      star_fix := fun x => x.2
      star_ne := ⟨x₀, fun h => by change cj w x₀ = x₀ at h; rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      norm_star := fun x => hneq _ _ (hval x)
      unram := by
        intro x
        by_cases hx : x = 0
        · exact ⟨0, by rw [hx]; rfl⟩
        · have hv0 : Valued.v x ≠ 0 := by simpa using hx
          refine ⟨⟨ϖ ^ (-WithZero.log (Valued.v x)), by
            change cj w (ϖ ^ (-WithZero.log (Valued.v x))) = ϖ ^ (-WithZero.log (Valued.v x)); rw [map_zpow₀, hϖf]⟩, ?_⟩
          change ‖x‖ = ‖ϖ ^ (-WithZero.log (Valued.v x))‖
          apply hneq
          rw [map_zpow₀, hϖv, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) from rfl,
            ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hv0] }
  have hcs : cj w = starRingEnd (w.adicCompletion E) := RingHom.ext fun _ => rfl
  have hth : ∀ h : GLw n w, (thL n w h).val = GlobalTheory.Tw.theta h.val := by
    intro h
    rw [thL, if_neg hs, hcs, thetaGL_val]
  have hnr : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
    rw [nrmL, if_neg hs, Units.val_mul, hcs, thetaGL_val]; rfl

  have hint : ∀ h : GLw n w, h ∈ GlobalTheory.LFun.KGL w n → (∀ i j, ‖h.val i j‖ ≤ 1) ∧ ‖h.val.det‖ = 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (GlobalTheory.GKFactor.UnitaryInt.mem_GLint_iff_entries (Ov E w) h).1 hh
    have hdet : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, M i j ∈ Ov E w) → M.det ∈ Ov E w := by
      intro M hM
      let M₀ : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨M i j, hM i j⟩
      have hM₀ : M = (Ov E w).subtype.mapMatrix M₀ := by ext i j; rfl
      rw [hM₀, ← RingHom.map_det]
      exact (M₀.det).2
    have d1 : ‖h.val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h1)
    have d2 : ‖(h⁻¹).val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h2)
    have hprod : ‖h.val.det‖ * ‖(h⁻¹).val.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    refine ⟨fun i j => (hle1 _).2 (h1 i j), ?_⟩
    nlinarith [norm_nonneg h.val.det, norm_nonneg (h⁻¹).val.det]
  have hintR : ∀ h : GLw n w, (∀ i j, ‖h.val i j‖ ≤ 1) → ‖h.val.det‖ = 1 → h ∈ GlobalTheory.LFun.KGL w n := by
    intro h h1 h2
    refine (GlobalTheory.GKFactor.UnitaryInt.mem_GLint_iff_entries (Ov E w) h).2 ⟨fun i j => (hle1 _).1 (h1 i j), fun i j => ?_⟩
    rw [Matrix.coe_units_inv]
    exact (hle1 _).1 (GlobalTheory.TwIntegral.intg_inv h1 h2 i j)
  obtain ⟨hy1, hy2⟩ := hint y hy
  obtain ⟨hg1, hg2⟩ := hint _ hyg
  have htw : GlobalTheory.Tw.twConj g.val y.val = (g⁻¹ * y * thL n w g).val := by
    rw [Units.val_mul, Units.val_mul, hth, Matrix.coe_units_inv]; rfl
  obtain ⟨u, v, hu, hv, huv⟩ := hbez
  rw [hnr] at huv
  obtain ⟨t, ⟨htu, htc⟩, k, hk1, hk2, hx⟩ := GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul (fixF (cj w)) (w.adicCompletion E) n
    y.val g.val hy1 hy2 ⟨u, v, fun i => (hle1 _).2 (hu i), fun i => (hle1 _).2 (hv i), huv⟩ g.isUnit
    (by rw [htw]; exact hg1) (by rw [htw]; exact hg2)
  have hku : IsUnit k := GlobalTheory.TwIntegral.isUnit_of_norm_det hk2
  refine ⟨htu.unit, ?_, hku.unit, hintR _ (by simpa using hk1) (by simpa using hk2), Units.ext ?_⟩
  · show htu.unit * y = y * thL n w htu.unit
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hth, IsUnit.unit_spec]
    exact htc
  · rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    exact hx

end GlobalTheory.InertUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZeta
section
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section

namespace GlobalTheory.FullRankCoinv

theorem continuous_of_mul_right_inv {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ) (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ho : IsOpen ((g⁻¹ * ·) ⁻¹' (H : Set G)) := hH.preimage (continuous_const.mul continuous_id)
  have hev : ∀ᶠ x in nhds g, f g = f x := by
    filter_upwards [ho.mem_nhds (by simpa using H.one_mem)] with x hx
    have := hf g (g⁻¹ * x) hx
    simpa using this.symm
  exact tendsto_const_nhds.congr' hev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gdet (n : ℕ) : Continuous (gdet : GL (Fin n) k → kˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert (Units.continuous_val (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
  · convert (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g
    show (((gdet g)⁻¹ : kˣ) : k) = _
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _

theorem continuous_char_apow (n : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν) (z : ℂ) :
    Continuous fun g : GL (Fin n) k => (ν (gdet g) : ℂ) * apow (gdet g) z := by
  let H : Subgroup (GL (Fin n) k) := GlobalTheory.SplitWeil.KO k (Fin n) ⊓ ν.ker.comap Matrix.GeneralLinearGroup.det
  have hH : IsOpen (H : Set (GL (Fin n) k)) :=
    isOpen_KO.inter (hν.preimage (continuous_gdet (k := k) n))
  refine continuous_of_mul_right_inv H hH _ fun g h hh => ?_
  have h1 : ν (gdet h) = 1 := hh.2
  have h2 : apow (gdet h) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hh.1) z
  simp only [gdet_mul, map_mul, Units.val_mul, apow_mul, h1, h2, Units.val_one, mul_one]

theorem integrable_fibre (n d : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν)
    [MeasurableSpace k] [BorelSpace k] (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ fullRk k n d)
    (Y : Matrix (Fin n) (Fin d) k) :
    Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  obtain ⟨⟨hlc, hcs⟩, hrk⟩ := hΨ
  by_cases hY : Y.rank = n
  swap
  · have h0 : (fun g : GL (Fin n) k =>
        Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = 0 := by
      funext g
      have : (g.val * Y).rank = Y.rank :=
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
      rw [hrk _ (by rw [this]; exact hY)]; simp
    rw [h0]; exact integrable_zero _ _ _

  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin d) (Fin n) k, Y * R = 1 := by
    have hsurj : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hY
    obtain ⟨f, hf⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have := congrArg LinearMap.toMatrix' hf
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' Y.mulVecLin = Y from LinearMap.toMatrix'_toLin' Y] at this

  have hsupp : tsupport Ψ = Function.support Ψ := by
    refine (IsClosed.closure_eq ?_)
    convert (hlc.isOpen_fiber 0).isClosed_compl using 1
    ext x; simp [Function.support]
  have hrkS : ∀ X ∈ tsupport Ψ, X.rank = n := fun X hX => by
    by_contra h; rw [hsupp] at hX; exact hX (hrk X h)
  set K' : Set (Matrix (Fin n) (Fin d) k) := tsupport Ψ ∩ {X | X * R * Y = X}
  have hK' : IsCompact K' := hcs.inter_right
    (isClosed_eq ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const) continuous_id)
  have hunit : ∀ X ∈ K', IsUnit (X * R) := fun X hX => by
    have h1 : n ≤ (X * R).rank := by
      calc n = X.rank := (hrkS X hX.1).symm
        _ = (X * R * Y).rank := by rw [hX.2]
        _ ≤ (X * R).rank := Matrix.rank_mul_le_left _ _
    have h2 : (X * R).rank = Fintype.card (Fin n) := le_antisymm
      ((Matrix.rank_le_card_width _).trans (by simp)) (by simpa using h1)
    have hli : LinearIndependent k (X * R).row := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact h2.symm.trans (Matrix.rank_eq_finrank_span_row _)
    exact Matrix.linearIndependent_rows_iff_isUnit.1 hli
  classical
  let φ : Matrix (Fin n) (Fin d) k → GL (Fin n) k := fun X =>
    if h : IsUnit (X * R) then h.unit else 1
  have hφ : ∀ X ∈ K', (φ X).val = X * R := fun X hX => by simp [φ, hunit X hX]
  have hφc : ContinuousOn φ K' := by
    rw [(isEmbedding_val_GL (k := k) (n := Fin n)).isInducing.continuousOn_iff]
    exact (continuous_id.matrix_mul continuous_const).continuousOn.congr fun X hX => hφ X hX
  set S : Set (GL (Fin n) k) := {g | g.val * Y ∈ tsupport Ψ}
  have hSsub : S ⊆ φ '' K' := fun g hg => by
    have hX : g.val * Y ∈ K' := ⟨hg, show g.val * Y * R * Y = g.val * Y by rw [Matrix.mul_assoc g.val Y R, hR, Matrix.mul_one]⟩
    refine ⟨_, hX, Units.ext ?_⟩
    rw [hφ _ hX, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hSc : IsClosed S := (isClosed_tsupport Ψ).preimage (Units.continuous_val.matrix_mul continuous_const)
  have hS : IsCompact S := (hK'.image_of_continuousOn hφc).of_isClosed_subset hSc hSsub
  have hcont : Continuous (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) := by
    have h1 : Continuous fun g : GL (Fin n) k => Ψ (g.val * Y) :=
      hlc.continuous.comp (Units.continuous_val.matrix_mul continuous_const)
    refine (h1.mul (continuous_char_apow n ν hν ((Fintype.card (Fin d) : ℂ) / 2))).congr fun g => ?_
    simp only [Pi.mul_apply]; ring
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  refine hcont.integrable_of_hasCompactSupport (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (HasCompactSupport.intro hS fun g hg => ?_)
  rw [image_eq_zero_of_notMem_tsupport hg]; simp

end GlobalTheory.FullRankCoinv

theorem GlobalTheory.FullRankCoinv.integrable_fibre_target : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) :=
  fun _ _ _ _ _ _ _ n d ν hν Ψ hΨ Y => GlobalTheory.FullRankCoinv.integrable_fibre n d ν hν Ψ hΨ Y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningLastEven
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dif_neg h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

example : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := locFin_sumPl

end GlobalTheory.RealLift
end

