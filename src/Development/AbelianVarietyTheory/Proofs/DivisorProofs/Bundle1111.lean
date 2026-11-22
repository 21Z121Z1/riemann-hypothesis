import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialL
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ZetaProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_fin_getD_list (f : ℂˣ → ℂ) : ∀ l : List ℂˣ, ∏ a : Fin l.length, f (l.getD a 1) = (l.map f).prod
  | [] => by simp
  | b :: l => by
    rw [List.length_cons, Fin.prod_univ_succ]
    simp [prod_fin_getD_list f l]

theorem prod_fin_getD (m : Multiset ℂˣ) {n : ℕ} (hn : m.card = n) (f : ℂˣ → ℂ) :
    ∏ a : Fin n, f (m.toList.getD a 1) = (m.map f).prod := by
  have hl : m.toList.length = n := (Multiset.length_toList m).trans hn
  subst hl
  rw [prod_fin_getD_list]
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.prod_coe]

variable {D : D7}

open Classical in

def zetaParams (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (cμ : (AE D)ˣ →* Circle) :
    HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ := fun w a =>
  if OffS D S w then
    (((B w).toList.getD a 1 : ℂˣ) : ℂ) * ((((GlobalTheory.LFun.val cμ)⁻¹ w : ℂˣ)) : ℂ) * GlobalTheory.LFun.npow w (-((1 + (D.R.t : ℂ)) / 2))
  else 0

theorem re_neg_half : (-((1 + (D.R.t : ℂ)) / 2)).re = -((1 + (D.R.t : ℝ)) / 2) := by
  rw [show -((1 + (D.R.t : ℂ)) / 2) = ((-((1 + (D.R.t : ℝ)) / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem norm_zetaParams_le {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.r) :
    ‖zetaParams S B cμ w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2) := by
  unfold zetaParams
  split_ifs with hw
  · have ha : (a : ℕ) < (B w).toList.length := by rw [Multiset.length_toList, hcard w hw]; exact a.2
    have hβ : (B w).toList.getD a 1 ∈ B w := by
      rw [List.getD_eq_getElem _ _ ha]
      exact Multiset.mem_toList.1 (List.getElem_mem ha)
    have hN : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := two_le_absNorm w
      linarith
    rw [norm_mul, norm_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one, mul_one,
      GlobalTheory.LFun.norm_npow, re_neg_half, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right (hb w hw _ hβ) (Real.rpow_nonneg hN.le _)
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem eulerOff_zetaParams {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) :
    eulerOff D S (zetaParams S B cμ) = GlobalTheory.LFun.LSD D S B cμ ((1 + (D.R.t : ℂ)) / 2) := by
  set x := zetaParams S B cμ with hxdef
  have hx := norm_zetaParams_le cμ hcard hb
  obtain ⟨h1, h2, -⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hm : Multipliable fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ := by
    have := multipliable_one_add_of_summable (f := fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ - 1)
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h2.mul_left 2))
    · simpa using this
    · have hx2 : ‖x p.1.1 p.2‖ ≤ 1 / 2 := h1 p
      have h3 : 1 / 2 ≤ ‖1 - x p.1.1 p.2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x p.1.1 p.2)
        rw [norm_one] at this
        linarith
      have hne : 1 - x p.1.1 p.2 ≠ 0 := fun h => by rw [h, norm_zero] at h3; linarith
      have e : (1 - x p.1.1 p.2)⁻¹ - 1 = x p.1.1 p.2 * (1 - x p.1.1 p.2)⁻¹ := by
        field_simp
        ring
      have h4 : ‖1 - x p.1.1 p.2‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      rw [e, norm_mul, norm_inv]
      nlinarith [norm_nonneg (x p.1.1 p.2)]
  have hp := hm.hasProd.prod_fiberwise fun b => hasProd_fintype _
  rw [eulerOff, ← hp.tprod_eq]
  show _ = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2)
  rw [GlobalTheory.LFun.eulerProd]
  let e : {w // OffS D S w} ≃ {w // w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} :=
    Equiv.subtypeEquivRight fun w => (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff S w).trans (by simp [GlobalTheory.LFun.above])
  rw [← e.tprod_eq]
  refine tprod_congr fun w => ?_
  show _ = GlobalTheory.LFun.locL _ w.1 _
  rw [GlobalTheory.LFun.locL_twist, ← prod_fin_getD (B w.1) (hcard w.1 w.2)]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [hxdef, zetaParams, if_pos w.2]

end GlobalTheory.LowRow.ZetaProd

namespace GlobalTheory.LowRow

theorem finiteZetaC_of_finiteZetaL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    FiniteZetaL R F → FiniteZetaC R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨B, hsys, hb, -, hsum⟩ := hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  have hcard : ∀ w, OffS D (finS R t) w → (B w).card = D.R.r := fun w hw => by
    have hv : w.under (𝓞 D.host.F) ∉ ((finS R t : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
      simpa using (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff _ w).1 hw
    rcases hsys _ hv w rfl with ⟨-, h, -⟩ | ⟨-, τ, ϖ, α, -, -, h, -⟩
    · exact h
    · rw [h]
      exact GlobalTheory.LGrp.card_bcParam _ α
  refine ⟨ZetaProd.zetaParams (finS R t) B cμ, ZetaProd.norm_zetaParams_le cμ hcard hb, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  rw [ZetaProd.eulerOff_zetaParams cμ hcard hb]
  exact hsum U₁ h₁ U₂ h₂ v₁ v₂

end GlobalTheory.LowRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.FlagZ

open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic in

theorem curveDeg_restr_flDet_nonneg : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)) (Z : Scheme.{0})
    (i : Z ⟶ Fl ι N) [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) →
    topologicalKrullDim Z = 1 → ∃ (r : ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B.ι → Z.functionFieldˣ)
      (hr : IsRatSec ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B r),
      0 ≤ ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).curveDeg hr := by
  intro ι _ N τ l Z i _ _ _ hc hd
  have hX : GlobalTheory.IsArithVar (i ≫ flStr ι N) 0 :=
    ⟨inferInstance, inferInstance, inferInstance,
      isProjOver_comp_of_isClosedImmersion i (isProjOver_str _ _), (flat_int_iff_charZero _).2 hc, by simpa using hd⟩
  obtain ⟨I, hI⟩ : ∃ I, i (genericPoint Z) ∈
      nonzeroLocus (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) := by
    have hm : i (genericPoint Z) ∈ (⊤ : (Fl ι N).Opens) := trivial
    rw [← iSup_nonzeroLocus_plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l)] at hm
    exact TopologicalSpace.Opens.mem_iSup.1 hm
  have hu : genericPoint Z ∈ nonzeroLocus (secPull (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) i) := by
    rw [nonzeroLocus_secPull]
    exact hI
  have h0 : ∀ σ (y : CxPts (i ≫ flStr ι N) σ), y ∈ ptsIn _ σ
      (nonzeroLocus (secPull (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I) i)) := fun σ y => by
    rw [mem_ptsIn]
    have e := hX.under_eq_genericPoint y
    simp only [under] at e
    rw [e]
    exact hu
  refine ⟨_, isRatSec_ratOfSec _ hu, ?_⟩
  rw [HermLB.curveDeg_sec (L := (flDet τ l : GlobalTheory.HermLB (flStr ι N))) i _ hu h0]
  refine sub_nonneg.2 (le_trans ?_ (finsum_nonneg fun z => mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
    (Real.log_natCast_nonneg _)))
  rw [← neg_nonneg, ← finsum_neg_distrib]
  refine finsum_nonneg fun σ => ?_
  rw [← finsum_neg_distrib]
  refine finsum_nonneg fun y => ?_
  have h1 := plSec_mem_smallSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I σ
    (PtsOver.map i rfl _ y)
  have h2 := Weight.nsq_nonneg (((flDet τ l : GlobalTheory.HermLB (flStr ι N))).φ σ)
    (secVal _ σ (plSec (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (τ, l) I)) (PtsOver.map i rfl _ y)
  have h3 := Real.log_nonpos h2 h1
  linarith

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOrbitMapSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open IsLocalRing

namespace GlobalTheory.FlagZ

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))

theorem exists_eq_flagPt_of_valuationRing (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (s : Sp K ⟶ Sp (GLRing ι N)) (t : Sp V ⟶ Part a l)
    (w : s ≫ orbit a l = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ t) :
    ∃ k : ι → GL (Fin N) V, t = flagPt a l k := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective s
  let g : ι → GL (Fin N) K := fun τ => GeneralLinearGroup.map ψ.hom (univGL ι N τ)
  have hg : Spec.map ψ ≫ orbit a l = flagPt a l g := by
    rw [← flagPt_univGL]
    exact spMap_flagPt a l ψ.hom _
  choose k b hb hkb using fun τ => GlobalTheory.ValIwasawa.iwasawa V K N (g τ)
  have e : flagPt a l g = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ flagPt a l k := by
    have : g = (fun τ => GeneralLinearGroup.map (algebraMap V K) (k τ)) * b := funext hkb
    rw [this, flagPt_mul a l _ b fun c i j h₁ h₂ => hb (a c) (h₁.trans_le h₂)]
    exact (spMap_flagPt a l (algebraMap V K) k).symm
  refine ⟨k, ?_⟩
  have hu := GlobalTheory.ProjSpace.existsUnique_extend_of_isProjOver (V := V) (K := K) (isProjOver_str a l)
    (Int.castRingHom V) (flagPt a l g) (toZ_ext _ _)
  exact hu.unique ⟨toZ_ext _ _, w.symm.trans hg⟩ ⟨toZ_ext _ _, e.symm⟩

theorem mem_range_orbit_of_specializes (x' : Sp (GLRing ι N)) (y : Part a l) (h : orbit a l x' ⤳ y) :
    y ∈ Set.range (orbit a l) := by
  let φ : (Part a l).presheaf.stalk y ⟶ (Sp (GLRing ι N)).residueField x' :=
    (Part a l).presheaf.stalkSpecializes h ≫ (orbit a l).stalkMap x' ≫ (Sp (GLRing ι N)).residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing φ.hom
  let χ : (Part a l).presheaf.stalk y ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : (Sp (GLRing ι N)).fromSpecResidueField x' ≫ orbit a l =
      Spec.map (CommRingCat.ofHom (algebraMap A ((Sp (GLRing ι N)).residueField x'))) ≫
        Spec.map χ ≫ (Part a l).fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨k, hk⟩ := exists_eq_flagPt_of_valuationRing a l A ((Sp (GLRing ι N)).residueField x') _ _ w
  refine ⟨spMap (evalGL k) (closedPoint A), ?_⟩
  have h₁ : Spec.map χ (closedPoint A) = closedPoint ((Part a l).presheaf.stalk y) :=
    comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
  have h₂ : (Spec.map χ ≫ (Part a l).fromSpecStalk y) (closedPoint A) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg ((Part a l).fromSpecStalk y) h₁).trans (Part a l).fromSpecStalk_closedPoint)
  rw [hk] at h₂
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h₂

theorem surjective_orbit : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)),
    Function.Surjective (orbit a l) := by
  intro ι κ _ _ N a l y
  have hd : DenseRange (orbit a l) := (orbit a l).denseRange
  have hη := (genericPoint_spec (Sp (GLRing ι N))).image (orbit a l).continuous
  rw [Set.image_univ, hd.closure_range] at hη
  exact mem_range_orbit_of_specializes a l _ y (hη.specializes (Set.mem_univ y))

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBaseChangeSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SecFlatBC

theorem pullLE_ofSec {X X' : Scheme.{0}} {L : LB X} (τ : L.Sec) (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens)
    (e : V' ≤ π ⁻¹ᵁ V) :
    AbLaw.SecOn.pullLE L π V V' e (LB.ofSec τ V) = LB.ofSec (Cartier.secPull τ π) V' := by
  refine LB.sec_ext fun j => ?_
  rw [AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]
  simp only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sum_smul_f {X' : Scheme.{0}} {R' : Type} [CommRing R'] (f' : X' ⟶ Sp R') {M : LB X'} {n : ℕ}
    (c : Fin n → R') (τ : Fin n → M.Sec) (i : M.ι) :
    (∑ a, AbLaw.cst f' ⊤ (c a) • τ a).f i = ∑ a, cstOn f' _ (c a) * (τ a).f i := by
  let F : M.Sec →+ Γ(X', M.U i) := ⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩
  change F _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _
  rw [show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]
  rfl

theorem exists_sum_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  intro R R' _ _ φ X X' f f' π _ _ L hφ H hL σ
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  have H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := H
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := GlobalTheory.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) :=
    GlobalTheory.isAffineOpen_finset_biInf hD
  have hc' := AbLaw.PerfOfModel.iSup_preimage π hc
  let E := AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'
  let E₀ := AbLaw.CechOne.secKerEquiv L f hc
  let d := ((AbLaw.cechLB f L D).d 0 1).hom
  obtain ⟨x, hx, hxy⟩ := (AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2
  have hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R') :=
    Module.Flat.ker_lTensor_eq (R := R) R' R' d
  rw [hker] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let e := S.equivFin
  refine ⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩

  have key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π := by
    apply E.injective
    apply Subtype.ext
    rw [← hxy, map_sum, map_sum, map_sum, AddSubmonoid.coe_finset_sum,
      ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]
    funext s
    have hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s =
        AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i)) := by
      rw [← AbLaw.CechOne.secKerEquiv_val L f hc]
      exact congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm
    change (e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) =
      (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s
    rw [hk, AbLaw.CechOne.secKerEquiv_val]
    change _ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _
    rw [AbLaw.SecOnR.pull_of, pullLE_ofSec]
    rfl
  intro i
  rw [key, sum_smul_f]

end GlobalTheory.SecFlatBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatZeroFromResolutionAndGaga
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.DFormPos

theorem sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
    (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s := by
  intro p _ G B y s hsim0
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  set h := G.gram v
  set A := G.psi v (y : G.C)
  set Ai := G.psi v ((y⁻¹ : G.Cˣ) : G.C)
  set Pb := G.psi v (B.β : G.C)
  set Bm := G.psi v ((B.β⁻¹ : G.Cˣ) : G.C)
  set c : ℂ := ((s : ℚ) : ℂ)
  have hsim := congrArg (G.psi v) hsim0
  have hc : G.psi v (algebraMap ℚ G.C s) = c • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j; simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, c]
  rw [map_mul, map_mul, map_mul, hc] at hsim
  change A * Pb * G.psi v (G.star (y : G.C)).unop = _ at hsim
  rw [G.psi_star, Matrix.smul_mul, Matrix.one_mul] at hsim
  have hBβ : Bm * Pb = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hβB : Pb * Bm = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hAiA : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hhi : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hdet
  have e1 : Aᴴ * h = c • (h * Bm * Ai * Pb) := by
    have := congrArg (fun M => h * Bm * Ai * M) hsim
    calc Aᴴ * h = h * Bm * Ai * (A * Pb * (h⁻¹ * Aᴴ * h)) := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc (h * Bm) Ai A, hAiA, Matrix.mul_one, Matrix.mul_assoc h Bm Pb, hBβ, Matrix.mul_one, hhi,
            Matrix.one_mul]
      _ = _ := by rw [this, Matrix.mul_smul]
  have key : Aᴴ * (h * Bm) * A = c • (h * Bm) := by
    rw [← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pb Bm A, hβB, Matrix.one_mul, hAiA, Matrix.mul_one]
  obtain ⟨x, hx⟩ : ∃ x : Fin G.n → ℂ, x ≠ 0 := ⟨Pi.single ⟨0, G.n_pos⟩ 1, by simp⟩
  have hAx : A *ᵥ x ≠ 0 := fun h0 => hx (by
    have := congrArg (Ai *ᵥ ·) h0
    simpa [Matrix.mulVec_mulVec, hAiA] using this)
  have e2 : star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x)) = c * (star x ⬝ᵥ ((h * Bm) *ᵥ x)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc] at key ⊢
    rw [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcr : c = ((s : ℝ) : ℂ) := by simp [c]
  have h1 := B.posR v x hx
  have h2 := B.posR v _ hAx
  change (_ → 0 < (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re) ∧ (_ → (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re < 0) at h1
  change (_ → 0 < (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re) ∧
    (_ → (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re < 0) at h2
  rw [e2, hcr, Complex.re_ofReal_mul] at h2
  have hs : (0 : ℝ) < s := by
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have a1 := h1.1 hv
      have a2 := h2.1 hv
      by_contra hn
      push_neg at hn
      nlinarith
    · have a1 := h1.2 hv
      have a2 := h2.2 hv
      by_contra hn
      push_neg at hn
      nlinarith
  exact_mod_cast hs

end GlobalTheory.LKDef.DFormPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTop
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

example : ∀ (P Q R S : ℕ) (x : ℂ), Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := span_harm2_sup_coinv_eq_univ

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadraticStatement
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  first | exact @GlobalTheory.RealLift.QuadFock.quad_fock | exact GlobalTheory.RealLift.QuadFock.quad_fock | (intros; apply GlobalTheory.RealLift.QuadFock.quad_fock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOperaStatement
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  first | exact @GlobalTheory.MulVarSpan.mulX_mem_span | exact GlobalTheory.MulVarSpan.mulX_mem_span | (intros; apply GlobalTheory.MulVarSpan.mulX_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominatorsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formGroup_testFunction_support_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  first | (exact @GlobalTheory.LKCx.BoundedDen.main) | (exact GlobalTheory.LKCx.BoundedDen.main) | (intros; apply GlobalTheory.LKCx.BoundedDen.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacterStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  first | exact @GlobalTheory.KSp.GaussMain.hasGauss_herm | exact GlobalTheory.KSp.GaussMain.hasGauss_herm | (intros; apply GlobalTheory.KSp.GaussMain.hasGauss_herm <;> assumption)
end

