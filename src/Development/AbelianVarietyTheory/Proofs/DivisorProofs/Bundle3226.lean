import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoi
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem finite_orbits_of_finite_pts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  intro p _ G v wt Kf f hfi K' f' hfi' β x t hx hT
  let F : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
    Quot.lift (orbOfDat G v β x t hx Kf K') (fun a b h => orbOfDat_eq_of_same G v β x t hx _ _ h)
  let PL : Pts G v β x t hx Kf K' → Prop :=
    Quot.lift (DatWt G v β x t hx f f') (fun a b h => propext (datWt_iff_of_same G v β x t hx _ _ hfi hfi' h))
  refine (hT.image F).subset ?_
  rintro o ⟨y, hy⟩
  unfold cxF at hy
  split_ifs at hy with hc
  on_goal 2 => exact absurd rfl hy
  let d : Dat G v β := (LeftCosets.rep _ _ (Quotient.out o).1,
    ⟨Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)), hc.1⟩)
  have hd : DatWt G v β x t hx f f' d := ⟨y, hc.2, left_ne_zero_of_mul hy⟩
  refine ⟨Quot.mk _ d, ?_, ?_⟩
  · have e : PL (Quot.mk _ (Quot.out (Quot.mk (Same G v β x t hx Kf K') d))) = PL (Quot.mk _ d) :=
      congrArg PL (Quot.out_eq _)
    exact (e : DatWt G v β x t hx f f' _ = DatWt G v β x t hx f f' d).mpr hd
  · show orbOfDat G v β x t hx Kf K' d = o
    simp only [orbOfDat, d, LeftCosets.mk_rep]
    convert Quotient.out_eq' o using 2
    exact Prod.ext rfl (Projectivization.mk_rep _)

end GlobalTheory.CxUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.CycLoc

theorem length_quot_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {e a}) := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq

theorem finite_height_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (a : R) (ha : a ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) fun _ _ _ _ h => PrimeSpectrum.ext h).subset ?_
  rintro p ⟨hp, hap⟩
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q hq hqp => ?_⟩
  by_contra hn
  have := hq.1
  have h1 : q < p.asIdeal := lt_of_le_not_ge hqp hn
  have h0 : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.2 fun h =>
    ha (by simpa [h] using (Ideal.span_singleton_le_iff_mem _).1 hq.2)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  rw [hp] at e1
  have : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := (add_le_add_left e0 1).trans e1
  rw [Ideal.height_bot] at this
  exact absurd this (by decide)

theorem stalk_equiv (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x p ∈ U) (hx : x ∈ U) (s : Γ(X, U)),
        e (X.presheaf.germ U _ hq s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) (X.presheaf.germ U x hx s) := by
  let y : Spec (X.presheaf.stalk x) := p
  have := GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  refine Eq.trans ?_ h2
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem specializes_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨p, rfl⟩

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨e, -⟩ := stalk_equiv X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

theorem mem_nonzeroLocus_iff_notMem {X : Scheme.{0}} {A : LB X} (s : A.Sec) {i : A.ι} {x : X} (hi : x ∈ A.U i)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ nonzeroLocus s ↔ X.presheaf.germ _ x hi (s.f i) ∉ p.asIdeal := by
  have hzi : X.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk X x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv X x p
  rw [Cartier.mem_nonzeroLocus_iff s i hzi, Scheme.mem_basicOpen _ _ _ hzi, ← MulEquiv.isUnit_map e, he _ hzi hi,
    IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal, Ideal.mem_primeCompl_iff]

theorem ker_stalkMap_clo (X : Scheme.{0}) (z : X) (w : clo z) (p : PrimeSpectrum (X.presheaf.stalk (cloι z w)))
    (hp : X.fromSpecStalk (cloι z w) p = z) : RingHom.ker ((cloι z).stalkMap w).hom = p.asIdeal := by
  let g : PrimeSpectrum ((clo z).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : (clo z).fromSpecStalk w g = genericPoint (clo z) := by
    have h := coheight_fromSpecStalk (clo z) w g
    rw [show g.asIdeal.height = 0 from Ideal.height_bot, Order.coheight_eq_zero] at h
    exact ((genericPoint_specializes _).antisymm (h (show _ ≤ genericPoint (clo z) from genericPoint_specializes _))).eq.symm
  have h : X.fromSpecStalk (cloι z w) (Spec.map ((cloι z).stalkMap w) g) = cloι z ((clo z).fromSpecStalk w g) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f => f g)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (cloι z) (x := w))).trans (Scheme.Hom.comp_apply _ _ _))
  rw [hg, cloι_genericPoint] at h
  have h' := (X.fromSpecStalk (cloι z w)).isEmbedding.injective (h.trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal h'

theorem germ_secPull {X V : Scheme.{0}} {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((GlobalTheory.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem coheight_one_iff (hq : IsAmb q) {z : Y} (w : clo z) (hz : Order.coheight z = 1) :
    Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2 := by
  have hB := GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨m, hm⟩ := hB.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint Y)
  have hY : topologicalKrullDim Y = d := (hB.2.2.2.2.2 Y d).1 hd
  cases d with
  | zero =>
    obtain ⟨d', -, hd'⟩ := hm z
    have := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq 0 hY z d' hd'
    rw [hz] at this
    simp at this
  | succ e => exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).2 z w hz).2

theorem germ_ne_zero {A : LB Y} {s : A.Sec} (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y} (hi : x ∈ A.U i) :
    Y.presheaf.germ _ x hi (s.f i) ≠ 0 := fun h0 =>
  fnOf_sec_ne_zero hs (gen_mem hi) ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))

variable [IsLocallyNoetherian Y]

theorem mult_eq {A : LB Y} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y}
    (hi : x ∈ A.U i) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    (divOfSec hA s hs).mult (Y.fromSpecStalk x p) = (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
        (Y.presheaf.germ _ x hi (s.f i))})).toNat := by
  have hzi : Y.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk Y x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv Y x p
  rw [mult_divOfSec ((coheight_fromSpecStalk Y x p).trans hp) hzi, length_quot_equiv _ _ e, he _ hzi hi]

theorem resCyc_eq (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) {j : B.ι} {x : Y} (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1)
    (ht : Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) {z : Y} (hz : Y.fromSpecStalk x p = z) :
    resCyc hB t (Set.indicator {x} 1) z = (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
      ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat := by
  have hzx : z ⤳ x := hz ▸ specializes_fromSpecStalk Y x p
  have hz1 : Order.coheight z = 1 := hz ▸ (coheight_fromSpecStalk Y x p).trans hp
  have hzt : z ∈ nonzeroLocus t := hz ▸ (mem_nonzeroLocus_iff_notMem t hj p).2 ht
  obtain ⟨w, rfl⟩ : x ∈ Set.range (cloι z) :=
    hzx.mem_closed (cloι z).isClosedEmbedding.isClosed_range ⟨_, cloι_genericPoint z⟩
  have h : genericPoint (clo z) ∈ nonzeroLocus (GlobalTheory.secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rwa [cloι_genericPoint]
  have hw : w ∈ (B.pull (cloι z)).U fun _ => j := Set.mem_iInter.2 fun _ => hj
  have hk := ker_stalkMap_clo Y z w p hz
  let e : (Y.presheaf.stalk (cloι z w) ⧸ p.asIdeal) ≃+* (clo z).presheaf.stalk w :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective ((cloι z).stalkMap_surjective w))
  rw [resCyc, dif_pos h, finsum_eq_single _ w fun w' hw' => by
    rw [Set.indicator_of_notMem (s := {cloι z w}) (a := cloι z w')
      (fun e => hw' ((cloι z).isClosedEmbedding.injective (Set.mem_singleton_iff.1 e))), mul_zero],
    Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    mult_divOfSec ((coheight_one_iff hq w hz1).2 hx) hw, germ_secPull t _ w j hj, length_quot_equiv _ _ e, Int.cast_natCast]
  rfl

theorem of_term_ne_zero (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x z : Y}
    (h : ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z ≠ 0) :
    Order.coheight x = 2 ∧ Order.coheight z = 1 ∧ z ∉ nonzeroLocus s ∧ z ⤳ x := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h1' : (divOfSec hA s hs).mult z ≠ 0 := by exact_mod_cast h1
  have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h1'
  rw [resCyc] at h2
  split_ifs at h2 with h3
  · obtain ⟨w, hw⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero h2)
    obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 hw
    have h6 : cloι z w = x := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h5)
    have h7 := CartierDiv.coheight_eq_one_of_mult_ne_zero (Int.cast_ne_zero.1 h4)
    refine ⟨h6 ▸ (coheight_one_iff hq w hz).1 h7, hz,
      fun h => notMem_supp_divOfSec.2 h (CartierDiv.mem_supp_of_mult_ne_zero h1'), ?_⟩
    have := (genericPoint_specializes w).map (cloι z).continuous
    rwa [cloι_genericPoint, h6] at this
  · exact absurd rfl h2

theorem finsum_eq (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x : Y} {i : A.ι} {j : B.ι} (hi : x ∈ A.U i) (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (P : Finset (PrimeSpectrum (Y.presheaf.stalk x)))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal)
    (hb : ∀ p ∈ P, Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) :
    ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z =
      ((∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (Y.presheaf.germ _ x hi (s.f i))})).toNat * (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
        ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat : ℕ) : ℝ) := by
  classical
  let ι : PrimeSpectrum (Y.presheaf.stalk x) → Y := fun p => Y.fromSpecStalk x p
  have hι : Function.Injective ι := (Y.fromSpecStalk x).isEmbedding.injective
  rw [finsum_eq_sum_of_support_subset (s := P.image ι), Finset.sum_image fun _ _ _ _ h => hι h, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [resCyc_eq hq hB t hj hx p ((hP p).1 hp).1 (hb p hp) rfl, mult_eq hA s hs hi p ((hP p).1 hp).1,
      Int.cast_natCast, Nat.cast_mul]
  · intro z hz
    obtain ⟨-, h1, h2, h3⟩ := of_term_ne_zero hq hA hB s t hs hz
    obtain ⟨p, rfl⟩ := (Scheme.range_fromSpecStalk (x := x)).ge h3
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hP p).2 ⟨(coheight_fromSpecStalk Y x p).symm.trans h1,
      not_not.1 (mt (mem_nonzeroLocus_iff_notMem s hi p).2 h2)⟩, rfl⟩)

end GlobalTheory.MixHt.CycLoc

namespace GlobalTheory.MixHt

open CycLoc in

theorem finsum_mult_resCyc_indicator_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst x
  by_cases hx : Order.coheight x = 2
  swap
  · rw [finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hA hB s t hs h).1,
      finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hB hA t s ht h).1]
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hA x
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB x
  have ha := germ_ne_zero hs hi
  have hb := germ_ne_zero ht hj
  have hP := fun p => (finite_height_one _ _ ha).mem_toFinset (a := p)
  have hQ := fun p => (finite_height_one _ _ hb).mem_toFinset (a := p)
  have key (p : PrimeSpectrum (Y.presheaf.stalk x)) (h1 : p.asIdeal.height = 1)
      (h2 : Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal) (h3 : Y.presheaf.germ _ x hj (t.f j) ∈ p.asIdeal) : False :=
    (hst _ ((coheight_fromSpecStalk Y x p).trans h1)).elim
      (fun h => (mem_nonzeroLocus_iff_notMem s hi p).1 h h2) fun h => (mem_nonzeroLocus_iff_notMem t hj p).1 h h3
  rw [finsum_eq hq hA hB s t hs hi hj hx _ hP fun p hp => key p ((hP p).1 hp).1 ((hP p).1 hp).2,
    finsum_eq hq hB hA t s ht hj hi hx _ hQ fun p hp h => key p ((hQ p).1 hp).1 h ((hQ p).1 hp).2]
  refine congrArg _ (GlobalTheory.T.length_sum_height_one_disjoint_divisors _ ?_ _ _ ha hb _ _ hP hQ (Finset.disjoint_left.2 fun p hp hp' =>
    key p ((hP p).1 hp).1 ((hP p).1 hp).2 ((hQ p).1 hp').2))
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.FirstChernW

open GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.LineForm.FirstChern

theorem smoothOn_atlas {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : Type} {U : Set (CxPts X.str σ)}
    {G : CxPts X.str σ → Matrix m m ℂ} (H : ∀ y ∈ U, MInfAt G y) (i j : m) :
    (atlas X σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1W_isForm_and_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  intro F _ σ X L ψ hψ
  have hφ : ∀ a (x : (atlas X σ).Pt), x.pt ∈ ptsIn X.str σ (L.U a) →
      ContDiffAt ℝ 2 (fun v => ψ.φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (hψ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (atlas X σ) (ι := Unit) (fun a => ptsIn X.str σ (L.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick ψ.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv X.str σ L a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ))
    (fun a => smoothOn_atlas fun y hy _ _ => (vInfAt_iff_cInfAt.2 (hψ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-ψ.φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv X.str σ L a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [ψ.trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, -, h3⟩ := hP (fld _ (c1W ψ)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick ψ.isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨h1, h3⟩

end GlobalTheory.ChernCalc.FirstChernW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_affine_polynomial_coords : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens), IsAffineOpen U → ∀ (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧ ∀ a, GlobalTheory.FlagCell.Spans (fl a) W (GlobalTheory.FlagCell.pullCol π (eU a) hW (GlobalTheory.FlagCell.uniR fun s => n ⟨a, s⟩)) := by
  first | exact @GlobalTheory.CellScheme.cell_affine | exact GlobalTheory.CellScheme.cell_affine | (intros; apply GlobalTheory.CellScheme.cell_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralRankTwo
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

section General

open ReciprocityTheory.L2DbarEstimates (V)

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem reDens_fn_mul (g : M → ℝ) (Φ : A.Fld) (i : A.ι) {z : V n} (hz : z ∈ (A.e i).target) :
    A.reDens (A.fn g * Φ) i z = g ((A.e i).symm z) * A.reDens Φ i z := by
  have h : (A.fn g * Φ) ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ =
      ((g ((A.e i).symm z) : ℝ) : ℂ) • Φ ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ := by
    rw [Algebra.smul_def]
    rfl
  simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hz]
  rw [h, dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc, Complex.re_ofReal_mul]
  rfl

theorem part_fn_mul_chart [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (g : M → ℝ) {Φ : A.Fld}
    (hΦ : A.IsForm Φ) (ε : ℤˣ) (i : A.ι) {U : Set (V n)} (hU : IsOpen U) (hUt : U ⊆ (A.e i).target) :
    A.part (A.fn g * Φ) ε ((A.e i).source ∩ A.e i ⁻¹' U) =
      ∫⁻ z in U, ENNReal.ofReal (g ((A.e i).symm z) * (((ε : ℤ) : ℝ) * A.reDens Φ i z)) := by
  have hWm : MeasurableSet ((A.e i).source ∩ A.e i ⁻¹' U) := ((A.e i).isOpen_inter_preimage hU).measurableSet
  have hcompat := A.ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i v)
    (fun i j y hi hj => by
      rw [reDens_fn_mul A g Φ i ((A.e i).map_source hi), reDens_fn_mul A g Φ j ((A.e j).map_source hj),
        (A.e i).left_inv hi, (A.e j).left_inv hj, A.reDens_compat hΦ i j y hi hj]
      ring)
  have hp : A.part (A.fn g * Φ) ε = ChartGlue.glueMeas A.e
      (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i (A.e i y))) := rfl
  have himg : A.e i '' ((A.e i).source ∩ A.e i ⁻¹' U) = U := by
    ext z
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
    · intro hz
      exact ⟨(A.e i).symm z, ⟨(A.e i).map_target (hUt hz), by simpa [(A.e i).right_inv (hUt hz)] using hz⟩,
        (A.e i).right_inv (hUt hz)⟩
  rw [hp, ChartGlue.glueMeas_apply _ _ A.holo hcompat i hWm Set.inter_subset_left,
    ChartGlue.chartMeas_apply_of_subset (A.e i) _ hWm Set.inter_subset_left, himg]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [(A.e i).right_inv (hUt hz), reDens_fn_mul A g Φ i (hUt hz)]
  congr 1
  ring

end General

theorem tendsto_integral_kernel_mul : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ Φ : (hY.atlas σ).Fld, (hY.atlas σ).IsForm Φ → (∀ x : (hY.atlas σ).Pt, v x.pt = 1 → dens (Φ x) = 0) →
      Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv Φ hΦ h0
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have main : ∀ ε : ℤˣ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
      ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε Set.univ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro ε
    have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
        ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε W) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      intro y
      obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
      obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
        GlobalTheory.T.local_density_bound_near_point d O (fun _ => 1) G s (c.e y) hO hcy continuousOn_const hG fun z hz => (hGp z hz).1
      obtain ⟨K, hK, hyK, hKN⟩ := exists_compact_subset hN hzN
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have hKO : K ⊆ O := hKN.trans hNO
      have hKt : K ⊆ c.e.target := hKO.trans hOt
      have hle' : Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          (volume.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
        refine le_trans ?_ hle
        simp only [ENNReal.ofReal_one]
        rw [show (fun _ : ReciprocityTheory.L2DbarEstimates.V (d + 1) => (1 : ENNReal)) = 1 from rfl, withDensity_one]
        exact Measure.map_mono_of_aemeasurable (Measure.restrict_mono hKN le_rfl)
          ((hF.mono hNO).aemeasurable hN.measurableSet)
      have hD : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z) K :=
        (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hΦ c)).mono hKt
      have hz0 : ∀ z ∈ K, GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) = 1 →
          ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z = 0 := by
        intro z hz h1
        have hzt : z ∈ ((hY.atlas σ).e c).target := hKt hz
        have := h0 ⟨(c, ((hY.atlas σ).e c).symm z), ((hY.atlas σ).e c).map_target hzt⟩
          (((hGp z (hKO hz)).2).trans h1)
        simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hzt, this, Complex.zero_re, mul_zero]
      have hlim := GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary _ volume K _ _ C hK (hF.mono hKO) hD hz0 hC hle'
      refine ⟨((hY.atlas σ).e c).source ∩ (hY.atlas σ).e c ⁻¹' interior K,
        ((hY.atlas σ).e c).isOpen_inter_preimage isOpen_interior, ⟨hy, hyK⟩, ?_⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => zero_le) fun t => ?_
      beta_reduce
      rw [part_fn_mul_chart (hY.atlas σ) _ hΦ ε c isOpen_interior (interior_subset.trans hKt)]
      refine le_trans (le_of_eq ?_) (lintegral_mono_set interior_subset)
      refine setLIntegral_congr_fun isOpen_interior.measurableSet fun z hz => ?_
      have := (hGp z (hKO (interior_subset hz))).2
      beta_reduce
      rw [← this]
      rfl
    choose W hWo hyW hW using loc
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
    have hs := tendsto_finset_sum T fun y _ => hW y
    rw [Finset.sum_const_zero] at hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun t => zero_le)
      fun t => (measure_mono hT).trans (measure_biUnion_finset_le T _)
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main 1)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main (-1))
  have := h1.sub h2
  rw [ENNReal.toReal_zero, sub_zero] at this
  exact this

end GlobalTheory.LineCos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangularStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cell_points_existsUnique_unitriangular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  first | exact @GlobalTheory.FlagCell2.cell_points_existsUnique | exact GlobalTheory.FlagCell2.cell_points_existsUnique | (intros; apply GlobalTheory.FlagCell2.cell_points_existsUnique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertySemiAbelianFlatBaseChangeDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussProperty_semiAbelian_flat_baseChange_dvr : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  first | exact @GlobalTheory.Desc.GaussBC.gauss_baseChange | exact GlobalTheory.Desc.GaussBC.gauss_baseChange | (intros; apply GlobalTheory.Desc.GaussBC.gauss_baseChange <;> assumption)
end

