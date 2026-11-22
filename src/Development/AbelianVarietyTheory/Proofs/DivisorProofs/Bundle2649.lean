import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeTo
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBaseStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  first | exact @GlobalTheory.PtExt.NatConst.const_of_natural | exact GlobalTheory.PtExt.NatConst.const_of_natural | (intros; apply GlobalTheory.PtExt.NatConst.const_of_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefCombinationOfPartialIndicators
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.HtNefAbel

theorem sum_mul_le (N : ℕ) : ∀ (g n : Fin N → ℤ) (c : ℤ),
    (∀ i : ℕ, i ≤ N → ∑ a : Fin N, (if a.val < i then g a else 0) ≤ 0) → Antitone n → (∀ a, c ≤ n a) →
    ∑ a, n a * g a ≤ c * ∑ a, g a := by
  induction N with
  | zero => intro g n c _ _ _; simp
  | succ N ih =>
    intro g n c hS hn hc
    have h1 := ih (fun a => g a.castSucc) (fun a => n a.castSucc) (n (Fin.last N)) (fun i hi => by
        have := hS i (hi.trans (Nat.le_succ N))
        rw [Fin.sum_univ_castSucc, if_neg (by simpa using hi), add_zero] at this
        simpa using this)
      (fun a b hab => hn (by simpa using hab)) (fun a => hn (Fin.le_last _))
    have h2 : ∑ a, g a ≤ 0 := by
      have := hS (N + 1) le_rfl
      simpa only [Fin.is_lt, if_true] using this
    have h3 := mul_le_mul_of_nonpos_right (hc (Fin.last N)) h2
    rw [Fin.sum_univ_castSucc]
    refine le_trans ?_ h3
    rw [Fin.sum_univ_castSucc (f := g), mul_add]
    exact add_le_add h1 le_rfl

theorem sum_neg_mul_nonneg (T : Type) [Fintype T] (N : ℕ) (g : T × Fin N → ℤ)
    (h₁ : ∀ τ : T, ∀ i : ℕ, i < N → 0 ≤ ∑ x : T × Fin N, (if x.1 = τ ∧ x.2.val < i then -1 else 0 : ℤ) * g x)
    (h₂ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then 1 else 0 : ℤ) * g x)
    (h₃ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then -1 else 0 : ℤ) * g x)
    (n : T → Fin N → ℤ) (hn : ∀ τ, Antitone (n τ)) : 0 ≤ ∑ x : T × Fin N, -n x.1 x.2 * g x := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  have e₂ : 0 ≤ ∑ a, g (τ, a) := by
    have := h₂ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  have e₃ : ∑ a, g (τ, a) ≤ 0 := by
    have := h₃ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  obtain ⟨c, hc⟩ := (Set.finite_range (n τ)).bddBelow
  have := sum_mul_le N (fun a => g (τ, a)) (n τ) c (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · have := h₁ τ i hi
        rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
        rw [← neg_nonneg, ← Finset.sum_neg_distrib]
        refine this.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
        by_cases h : a.val < i <;> simp [h]
      · simpa only [Fin.is_lt, if_true] using e₃) (hn τ) (fun a => hc ⟨a, rfl⟩)
  rw [le_antisymm e₃ e₂, mul_zero] at this
  simp only [neg_mul, Finset.sum_neg_distrib, neg_nonneg]
  exact this

theorem nefOver_comb_of_antitone : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro k _ X p d hX T _ N M l h₁ h₂ n hn Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let F : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have key (e : T × Fin N → ℤ) : topSelfIntersection κ ((ArInt.comb M e).B.pull i) 1 = ∑ x, e x * F (M x).icls := by
    change F (ArInt.comb M e).icls = _
    rw [icls_comb, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, smul_eq_mul]
  rw [key]
  exact sum_neg_mul_nonneg T N _ (fun τ j hj => key _ ▸ h₁ τ j hj Z i κ hd) (fun τ => key _ ▸ (h₂ τ).1 Z i κ hd)
    (fun τ => key _ ▸ (h₂ τ).2 Z i κ hd) n hn

end GlobalTheory.HtNefAbel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

theorem nefFib_of_cls_eq_ample [Module.Finite ℤ k] [IsProper p] {M : HermLB p} {B : LB X} (hB : IsAmpleLB B)
    (h : cls M.B M.isLB = cls B hB.isLB) : ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (B.pull i) (pull_isLB hB.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull hB.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB hB.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  have hA := hB.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e' : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e']; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

open GlobalTheory.ArInt

theorem exists_nefFib_twists : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)),
    IsProjOver p → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ H : HermLB p,
      ∀ (X' : Scheme.{0}) (q : X' ⟶ Sp (𝓞 F)), IsProjOver q → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q),
        NefFib (H.pull π hπ) ∧ ∀ i, NefFib ((H.pull π hπ).tens ((L i).pull π hπ)) ∧
          NefFib ((H.pull π hπ).tens ((L i).pull π hπ).dual) := by
  intro F _ _ X p hp ι _ L
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  obtain ⟨N, j, hj, hjp⟩ := hp
  let A : HermLB p := (hermitianTwistingSheaf (𝓞 F) N).pull j hjp
  have hA : IsAmpleLB A.B := (isAmple_projective_O_one (𝓞 F) N).pull_of_isClosedImmersion j
  obtain ⟨t, h0, h1, h2⟩ := ((AmpleDominates.eventually_isAmpleLB p hA (LB.isLB_triv X)).and
    ((Filter.eventually_all.2 fun i =>
        AmpleDominates.eventually_isAmpleLB p hA (isLB_dual (L i).isLB)).and
      (Filter.eventually_all.2 fun i => AmpleDominates.eventually_isAmpleLB p hA (L i).isLB))).exists
  let H : HermLB p := A.pow t
  have cP : cls (lbPow A.B t) (isLB_lbPow A.isLB t) = cls H.B H.isLB := rfl
  have nH : NefFib H := nefFib_of_cls_eq_ample h0 (by
    rw [cls_div (isLB_lbPow A.isLB t) (LB.isLB_triv X), ← cP]
    exact (sub_zero _).symm)
  have nT (i : ι) : NefFib (H.tens (L i)) := nefFib_of_cls_eq_ample (h1 i) (by
    rw [cls_div (isLB_lbPow A.isLB t) (isLB_dual (L i).isLB), cls_dual (L i).isLB, sub_neg_eq_add, cP]
    rfl)
  have nD (i : ι) : NefFib (H.tens (L i).dual) := nefFib_of_cls_eq_ample (h2 i) (by
    rw [cls_div (isLB_lbPow A.isLB t) (L i).isLB, sub_eq_add_neg,
      ← cls_dual (L i).isLB (isLB_dual (L i).isLB), cP]
    rfl)
  have hp : IsProjOver p := ⟨N, j, hj, hjp⟩
  refine ⟨H, fun X' q hq π hπ => ?_⟩
  refine ⟨ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ H nH, fun i => ⟨?_, ?_⟩⟩
  · refine nefFib_of_cls_eq ?_ (ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ _ (nT i))
    exact (cls_pull (isLB_tens H.isLB (L i).isLB) π _).trans
      (map_add (CechPic.pull π) (cls H.B H.isLB) (cls (L i).B (L i).isLB))
  · refine nefFib_of_cls_eq ?_ (ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ _ (nD i))
    refine (cls_pull (isLB_tens H.isLB (isLB_dual (L i).isLB)) π _).trans
      ((map_add (CechPic.pull π) (cls H.B H.isLB) (cls _ (isLB_dual (L i).isLB))).trans ?_)
    refine Eq.trans ?_ (cls_tens (pull_isLB H.isLB π) (isLB_dual (pull_isLB (L i).isLB π)) _).symm
    refine congrArg (CechPic.pull π (cls H.B H.isLB) + ·) ?_
    rw [cls_dual (L i).isLB, map_neg]
    exact (cls_dual (pull_isLB (L i).isLB π) (isLB_dual (pull_isLB (L i).isLB π))).symm

end GlobalTheory.AmpleTwistNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianBundlePullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm GlobalTheory.CechPic

namespace GlobalTheory.VertForm

theorem nefOver_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ),
    l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  intro k _ _ X Y p q hp hq π hπ L l hl hL Z i _ _ κ _ _ _ _ hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper q := hj' ▸ inferInstance
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := GlobalTheory.ArInt.topSelf_pull_nonneg l (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z' i' _ _ _ hd' => hL Z' i' (ZMod l) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rw [← topSelf_congr (ZMod l) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)] at h
  have e2 := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => (L.pull π hπ).B.pull i)
  rw [topSelf_def] at h ⊢
  rw [e2] at h
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h

end GlobalTheory.VertForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreNef

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)))

theorem isProjOver_fibre {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (hp : IsProjOver p) (l : ℕ) [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Algebra (ZMod l) Γ(Z, ⊤)] : IsProjOver (strHom (ZMod l) Z) := by
  obtain ⟨N, e, he, -⟩ := hp
  have hb : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have P₀ := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom k)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) :=
    MorphismProperty.of_isPullback P₀.flip hb
  have hZ : IsProjOver ((i ≫ e ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) ≫ PSpace.str ℤ N) :=
    GlobalTheory.isProjOver_comp_of_isFinite _ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨M, φ, hφ, -⟩ := hZ
  have P := GlobalTheory.ProjSpace.isPullback_baseChange M (Int.castRingHom (ZMod l))
  have hc : IsClosedImmersion (spMap (Int.castRingHom (ZMod l))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  have hcb : IsClosedImmersion (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) :=
    MorphismProperty.of_isPullback P.flip hc
  let ψ := P.lift φ (strHom (ZMod l) Z) (specZIsTerminal.hom_ext _ _)
  have hψ : ψ ≫ PSpace.str (ZMod l) M = strHom (ZMod l) Z := P.lift_snd _ _ _
  have hψ' : ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l)) = φ := P.lift_fst _ _ _
  have : IsClosedImmersion (ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) := by
    rw [hψ']; exact hφ
  exact ⟨M, ψ, IsClosedImmersion.of_comp_isClosedImmersion ψ
    (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))), hψ⟩

theorem isNef_pull_of_nefOver {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (l : ℕ)
    [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [Algebra (ZMod l) Γ(Z, ⊤)]
    (L : HermLB p) (hL : NefOver L l) : IsNef (ZMod l) (L.B.pull i) := by
  have hLi := LB.isLB_pull L.isLB i
  refine isNef_iff_isClosedImmersion.2 ⟨hLi, fun C c hc hC hd _ => ?_⟩
  letI := algebraΓAlong (ZMod l) c
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h := hL C (c ≫ i) (ZMod l) hd
  rw [interNumOn_eq_interNum_pull (fun r => rfl) (fun j => by fin_cases j; exact hLi)]
  rw [topSelfIntersection] at h
  refine h.trans_eq (interNum_congr_lbIso _ _ (fun _ => LB.isLB_pull L.isLB _)
    (fun j => by fin_cases j; exact LB.isLB_pull hLi c) fun j => ?_)
  fin_cases j
  exact lbIso_pull_comp L.isLB i c

theorem interNum_nonneg_of_nefOver : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (l : ℕ) [Fact l.Prime] (Z : Scheme.{0}) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)], topologicalKrullDim Z = D →
    ∀ N : Fin D → HermLB p, (∀ j, NefOver (N j) l) →
      0 ≤ interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i) := by
  intro hP k _ X _ p D hX l _ Z i _ _ _ hZ N hN
  haveI := hX.finite
  exact hP.q7.1.interNum_nonneg (isProjOver_fibre hX.isProjOver l i) hZ
    fun j => isNef_pull_of_nefOver l i (N j) (hN j)

end GlobalTheory.FibreNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSurjectivePullbackNef
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.VertForm

namespace GlobalTheory.NefDescent

theorem nefOver_of_primeField {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (l : ℕ)
    [Fact l.Prime]
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1) :
    NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hdim
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

theorem nefOver_of_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  intro k _ _ X Y p q hp hq π hπ hsurj L l hl hL
  haveI : Fact l.Prime := ⟨hl⟩
  refine nefOver_of_primeField L l ?_
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod l) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod l) f
  have h1 := hL _ i' (ZMod l) hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod l) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 = interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod l) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod l) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod l) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod l) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod l) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInductionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop), (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) → (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  first | exact @GlobalTheory.PDForm.pdPoly_forms_induction | exact GlobalTheory.PDForm.pdPoly_forms_induction | (intros; apply GlobalTheory.PDForm.pdPoly_forms_induction <;> assumption)
end

