import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ColsInLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat

variable {D : D7}

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (finIncl D).rTensor D.host.E

theorem lift_eq (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    lift D z = finEmb D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lift_finPart (z : AE D) (h : infPart D z = 0) : lift D (finPart D z) = z := by
  have key : ∀ z : AE D, z =
      (show Ainf D.host.F →ₗ[D.host.F] AF D.host.F from
        LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E (infPart D z) +
      lift D (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      change _ = (pairA D.host.F a.1 0) ⊗ₜ[D.host.F] e + (pairA D.host.F 0 a.2) ⊗ₜ[D.host.F] e
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero a.1).symm (zero_add a.2).symm
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  have := key z
  rw [h, map_zero, zero_add] at this
  exact this.symm

def col (V W : HSp D) (b : Fin V.rank) : (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ WO V W where
  toFun z := Matrix.of fun i j => if j = b then lift D (z i) else 0
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add]
    split_ifs <;> simp

theorem col_mem (V W : HSp D) (hV : V.gram = 1) (k : GA D W) (b : Fin V.rank)
    (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latGHat W k) :
    col V W b z ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    have hz' : z ∈ hat D.host.F (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) := by
      rw [← SetLike.mem_coe, GlobalTheory.MovedLat.hat_hLat]
      rw [gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1] at hz
      exact hz
    have hs : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      intro i _
      by_cases h : i = b
      · subst h; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have := rankOne_mem_latO V W _ _ a ha _ (pure_mem_hatL _ 1 (one_mem _) _ hs) _
      (GlobalTheory.PrincInLevel.swap_mem_hatL _ z hz')
    convert this using 1
    ext i j
    change (if j = b then lift D (((1 : Af D.host.F) ⊗ₜ a) * z i) else 0) = _
    simp only [rankOne, Matrix.of_apply, hV, cF_tmul, eToEAf, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.sum_tmul]
    have e : ∑ l, star ((Pi.single b 1 : Fin V.rank → D.host.E) l) *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) l j = if j = b then 1 else 0 := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    split_ifs
    · rw [lift_eq, map_mul, ← Algebra.TensorProduct.one_def, mul_one]
      rfl
    · simp
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem mem_latO_of_cols : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  intro D V W hV k x h0 hc
  have e : x = ∑ b, col V W b fun a => finPart D (x a b) := by
    ext i j
    rw [Matrix.sum_apply]
    change _ = ∑ b, if j = b then lift D (finPart D (x i b)) else 0
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    exact (lift_finPart _ (congrFun (congrFun h0 i) j)).symm
  rw [e]
  exact sum_mem fun b _ => col_mem V W hV k b _ (hc b)

end GlobalTheory.ColsInLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeUnimodular
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add, MulOpposite.unop_add, hx, hy, map_add, MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i
  rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finset_sum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open H0

theorem eq_zero_of_forall_algHom_eq_zero {E A : Type} (Ω : Type) [Field E] [CommRing A]
    [Algebra E A] [Algebra.Etale E A] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {a : A}
    (h : ∀ φ : A →ₐ[E] Ω, φ a = 0) : a = 0 := by
  have := Algebra.FormallyUnramified.finite_of_free E A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field E A
  have : IsArtinianRing A := .of_finite E A
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  let := Ideal.Quotient.field J
  let ψ : (A ⧸ J) →ₐ[E] Ω := IsAlgClosed.lift
  have := h (ψ.comp (Ideal.Quotient.mkₐ E J))
  rw [AlgHom.comp_apply, map_eq_zero_iff ψ ψ.toRingHom.injective] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

section Points

variable {k R : Type} [CommRing k] [CommRing R] {S : Scheme.{0}}

theorem evalPt_algX (q : S ⟶ Sp k) (x : Sp R ⟶ S) (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) :
    evalPt x U h (algX q U c) =
      evalPt (x ≫ q) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
  congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE x q ⊤ U ⊤ le_top h)

theorem evalPt_algX_of_eq (q : S ⟶ Sp k) (x : Sp R ⟶ S) {φ : k →+* R} (hx : x ≫ q = spMap φ)
    (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) : evalPt x U h (algX q U c) = φ c := by
  rw [evalPt_algX, hx, evalPt_spMap]

theorem H0.val_smul {q : S ⟶ Sp k} {N : LB S} {O : S.Opens} (x : Sp R ⟶ S) {φ : k →+* R}
    (hx : x ≫ q = spMap φ) (i : N.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ N.U i) (c : k)
    (f : H0 q N O) : val x i hO hi (c • f) = φ c * val x i hO hi f := by
  rw [base_smul, val_fun_smul, evalPt_algX_of_eq q x hx]

variable (R) in

abbrev PtsOver [Algebra k R] (q : S ⟶ Sp k) : Type :=
  {x : Sp R ⟶ S // x ≫ q = spMap (algebraMap k R)}

def ptsOverEquiv [Algebra k R] [IsAffine S] (q : S ⟶ Sp k) :
    letI := (algX q ⊤).toAlgebra
    PtsOver R q ≃ (Γ(S, ⊤) →ₐ[k] R) :=
  letI := (algX q ⊤).toAlgebra
  Equiv.ofBijective
    (fun x => ⟨evalPt x.1 ⊤ le_top, fun c => evalPt_algX_of_eq q x.1 x.2 ⊤ le_top c⟩)
    ⟨fun x y e => Subtype.ext (ext_evalPt (isAffineOpen_top S) le_top le_top
      (congrArg AlgHom.toRingHom e)), fun ψ => by
      obtain ⟨x, h, e⟩ := exists_evalPt_eq (isAffineOpen_top S) ψ.toRingHom
      refine ⟨⟨x, eq_spMap_of_evalPt _ _ fun c => ?_⟩, AlgHom.ext fun a => DFunLike.congr_fun e a⟩
      rw [← evalPt_algX q x ⊤ h, e]
      exact ψ.commutes c⟩

end Points

section FiniteEtale

variable {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E)

theorem etale_algX [IsAffine S] [Etale q] : (algX q ⊤).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top)

variable {N : LB S}

theorem exists_generator [IsFinite q] [Etale q] (hN : N.IsLB) : ∃ e : H0 q N ⊤,
    (Function.Bijective fun a : Γ(S, ⊤) => a • e) ∧ ∀ i, IsUnit (e.loc i) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  have : IsArtinianRing Γ(S, ⊤) := .of_finite E _
  obtain ⟨t, ht⟩ := exists_isGen_of_subsingleton_pic_top hN
  refine ⟨H0.ofSec q ⊤ (DVR.genSec t ht), ?_, fun i => (Units.isUnit (t.s i)).map (resG S inf_le_right)⟩
  have := isQuasicoherent_toMod hN
  exact (isFrame_iff_bijective (isAffineOpen_top S) _).1 (isFrame_genSec hN ht ⊤)

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] [IsFinite q] [Etale q]

omit [IsAlgClosed Ω] in

theorem finite_ptsOver : Finite (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  exact Finite.of_equiv _ (ptsOverEquiv q).symm

theorem finite_finrank_lineBundleSections_finiteEtale (hN : N.IsLB) :
    Module.Finite E (H0 q N ⊤) ∧ Module.finrank E (H0 q N ⊤) = Nat.card (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  obtain ⟨e, he, -⟩ := exists_generator q hN
  let ψ : Γ(S, ⊤) →ₗ[E] H0 q N ⊤ :=
    { toFun a := a • e
      map_add' a b := add_smul a b e
      map_smul' c a := mul_smul (algX q ⊤ c) a e }
  let φ := LinearEquiv.ofBijective ψ he
  exact ⟨.equiv φ, by
    rw [← φ.finrank_eq, Nat.card_congr (ptsOverEquiv q), natCard_algHom_eq_finrank_of_etale]⟩

variable {q Ω}

theorem H0.eq_zero_of_forall_val_eq_zero (hN : N.IsLB) (i : PtsOver Ω q → N.ι)
    (hi : ∀ x : PtsOver Ω q, ⊤ ≤ x.1 ⁻¹ᵁ N.U (i x)) {g : H0 q N ⊤}
    (h : ∀ x : PtsOver Ω q, val x.1 (i x) le_top (hi x) g = 0) : g = 0 := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  obtain ⟨e, he, hu⟩ := exists_generator q hN
  obtain ⟨a, rfl⟩ := he.2 g
  have : a = 0 := eq_zero_of_forall_algHom_eq_zero (E := E) Ω fun ψ => by
    obtain ⟨x, rfl⟩ := (ptsOverEquiv q).surjective ψ
    have := (val_fun_smul x.1 (i x) le_top (hi x) a e).symm.trans (h x)
    exact (((hu (i x)).map (evalPt x.1 _ _)).mul_left_eq_zero).1 this
  simp only [this, zero_smul]

end FiniteEtale

section Subscheme

variable {E : Type} [Field E] {Y : Scheme.{0}} {p : Y ⟶ Sp E} {I : Y.IdealSheafData} {B : LB Y}

theorem exists_chart_of_field {F : Type} [Field F] (hB : B.IsLB) (x : Sp F ⟶ Y) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ B.U i := by
  obtain ⟨i, hi⟩ := exists_chart hB (x (default : PrimeSpectrum F))
  exact ⟨i, fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) default z) ▸ hi⟩

theorem valOn_smul {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k}
    (x : Sp R ⟶ I.subscheme) {φ : k →+* R} (hx : x ≫ I.subschemeι ≫ p = spMap φ) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (c : k) (g : sectionsOnClosedSubscheme p B I) :
    valOn x i hi (c • g) = φ c * valOn x i hi g :=
  H0.val_smul x hx _ _ _ c g

variable [IsFinite (I.subschemeι ≫ p)] [Etale (I.subschemeι ≫ p)] (hB : B.IsLB)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]

include hB

theorem finite_H0On : Module.Finite E (sectionsOnClosedSubscheme p B I) :=
  (finite_finrank_lineBundleSections_finiteEtale _ (AlgebraicClosure E) (LB.isLB_pull hB _)).1

theorem finrank_H0On :
    Module.finrank E (sectionsOnClosedSubscheme p B I) = Nat.card (PtsOver Ω (I.subschemeι ≫ p)) :=
  (finite_finrank_lineBundleSections_finiteEtale _ Ω (LB.isLB_pull hB _)).2

variable {Ω} in

theorem eq_zero_of_forall_valOn_eq_zero (i : PtsOver Ω (I.subschemeι ≫ p) → B.ι)
    (hi : ∀ x : PtsOver Ω (I.subschemeι ≫ p), ⊤ ≤ (x.1 ≫ I.subschemeι) ⁻¹ᵁ B.U (i x))
    {g : sectionsOnClosedSubscheme p B I} (h : ∀ x : PtsOver Ω (I.subschemeι ≫ p), valOn x.1 (i x) (hi x) g = 0) : g = 0 :=
  H0.eq_zero_of_forall_val_eq_zero (LB.isLB_pull hB _) (fun x _ => i x) _ h

end Subscheme

example (D : ℕ) : Module.finrank ℚ (sectionsOnClosedSubscheme (CanonLB.affStr ℚ D) (AffineExample.triv ℚ D)
    (AffineExample.ideal MvPolynomial.X)) = 1 := by
  have := AffineExample.isIso_of_span (k := ℚ) (D := D) (g := MvPolynomial.X) rfl
  rw [finrank_H0On AffineExample.isLB_triv ℂ, Nat.card_eq_one_iff_exists]
  exact ⟨⟨spMap (algebraMap ℚ ℂ) ≫ inv _, by simp⟩, fun x => Subtype.ext
    ((IsIso.eq_comp_inv _).2 x.2)⟩

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagDomain_frames_eq_gramFrames_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  first | exact @GlobalTheory.HolDict.FdDom.dom_iff_frDoms | exact GlobalTheory.HolDict.FdDom.dom_iff_frDoms | (intros; apply GlobalTheory.HolDict.FdDom.dom_iff_frDoms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTheoremOfResolutionGaga
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_left_basis_through_algHom : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  intro L _ _ C _ _ _ ι
  letI : Module L C := Module.compHom C ι.toRingHom
  have hsmul : ∀ (l : L) (x : C), l • x = ι l * x := fun _ _ => rfl
  haveI : IsScalarTower ℚ L C := ⟨fun q l x => by
    rw [hsmul, hsmul, map_smul, smul_mul_assoc]⟩
  haveI : Module.Finite L C := Module.Finite.of_restrictScalars_finite ℚ L C
  let b := Module.finBasis L C
  refine ⟨Module.finrank L C, b, fun x => ⟨b.repr x, ?_, ?_⟩⟩
  · simp only [← hsmul]
    exact (b.sum_repr x).symm
  · intro c hc
    simp only [← hsmul] at hc
    rw [hc, b.repr_sum_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAfFixed

theorem rat_eventually_int (p : ℕ) (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q w ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  have h2 : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    h.mono fun w hw => by rwa [FiniteAdeleRing.algebraMap_apply] at hw
  exact (Subtype.val_injective.tendsto_cofinite).eventually h2

theorem basV_repr_one_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (c : G.C) (i) :
    (basV G v).repr ((1 : Qv v) ⊗ₜ[ℚ] c) i = algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem isIntV_one_tmul_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  intro p _ G c
  have h : ∀ i, ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ :=
    fun i => rat_eventually_int p _
  refine (Filter.eventually_all.2 h).mono fun v hv i => ?_
  rw [basV_repr_one_tmul]
  exact hv i

end GlobalTheory.OrbFinAfFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondenceStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_unit_correspondence : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ u y, FrIs θ V hr X x u y → IsUnitFr X y) ∧ (∀ y, IsUnitFr X y → ∃ u ∈ GinfC V, FrIs θ V hr X x u y) ∧ (∀ u, ∃ y, FrIs θ V hr X x u y) ∧ (∀ u y y', FrIs θ V hr X x u y → FrIs θ V hr X x u y' → y = y') ∧ ∀ u ∈ GinfC V, ∀ u' ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → FrIs θ V hr X x u' y → u = u' := by
  first | exact @GlobalTheory.UnitFrameReal.unit_frames | exact GlobalTheory.UnitFrameReal.unit_frames | (intros; apply GlobalTheory.UnitFrameReal.unit_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftUnitTimesCoord
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end

