import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKroneckerStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  first | exact @GlobalTheory.DefPt.tval_translate | exact GlobalTheory.DefPt.tval_translate | (intros; apply GlobalTheory.DefPt.tval_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExtProj

open Matrix

variable {W : Type} [CommRing W] {n : ℕ} {R' : Type} [CommRing R'] (β : W →+* R') (v : Fin n → R')

theorem act_one : ((1 : Matrix (Fin n) (Fin n) W).map β) *ᵥ v = (1 : R') • v := by
  rw [Matrix.map_one _ (map_zero β) (map_one β), one_mulVec, one_smul]

theorem act_add {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M + N).map β) *ᵥ v = (s + s') • v := by
  rw [Matrix.map_add _ (map_add β), add_mulVec, hM, hN, add_smul]

theorem act_sub {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M - N).map β) *ᵥ v = (s - s') • v := by
  rw [Matrix.map_sub _ (map_sub β), sub_mulVec, hM, hN, sub_smul]

theorem act_smul {M : Matrix (Fin n) (Fin n) W} {s : R'} (r : W) (hM : (M.map β) *ᵥ v = s • v) :
    ((r • M).map β) *ᵥ v = (β r * s) • v := by
  have : (r • M).map β = β r • M.map β := by ext; simp
  rw [this, Matrix.smul_mulVec, hM, smul_smul]

theorem act_mul {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M * N).map β) *ᵥ v = (s * s') • v := by
  rw [Matrix.map_mul, ← mulVec_mulVec, hN, mulVec_smul, hM, smul_smul, mul_comm]

theorem act_list {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (l : List κ) :
    (((l.map F).prod).map β) *ᵥ v = (l.map S).prod • v := by
  induction l with
  | nil => simpa using act_one β v
  | cons j l ih => simpa using act_mul β v (h j) ih

theorem act_finset {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (s : Finset κ) :
    ((∑ j ∈ s, F j).map β) *ᵥ v = (∑ j ∈ s, S j) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]; exact act_add β v (h j) ih

theorem act_finsupp {O : Type} (F : O → Matrix (Fin n) (Fin n) W) (S : O → R')
    (h : ∀ x, ((F x).map β) *ᵥ v = S x • v) (f : O →₀ W) :
    ((f.sum fun x r => r • F x).map β) *ᵥ v = (f.sum fun x r => β r * S x) • v :=
  act_finset β v _ _ (fun x => act_smul β v (f x) (h x)) f.support

theorem ext_mulVec {L : Type} [Field L] {M N : Matrix (Fin n) (Fin n) L} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

end GlobalTheory.LieExtProj

namespace GlobalTheory.LieExtProj
open Matrix

theorem rhoPart_splits_by_idempotents : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  intro W L _ _ _ _ _ O _ n a A ω tr nm ρ t hω hρ htω hcop hdisc hsplit
  classical
  have hu2 : (2 * ρ - tr) * (2 * ρ - tr) = ((tr ^ 2 - 4 * nm : ℤ) : W) := by
    push_cast; linear_combination 4 * hρ
  have hu : IsUnit (2 * ρ - (tr : W)) := isUnit_of_mul_isUnit_left (hu2 ▸ hdisc)
  obtain ⟨ui, hui⟩ := hu.exists_left_inv
  set P : Matrix (Fin n) (Fin n) W := ui • (A ω + (ρ - tr) • 1) with hPdef

  have hf : ∀ i j, ∃ f : O →₀ W, i ≠ j →
      (f.sum fun x r => r * t i x) - (f.sum fun x r => r * t j x) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : W) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hcop i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      refine ⟨f, fun _ => ?_⟩
      rw [← hf, ← Finsupp.sum_sub]
      simp [Finsupp.sum, smul_eq_mul, mul_sub]
  choose f hf using hf
  let Z : Fin a → Fin a → Matrix (Fin n) (Fin n) W := fun i j =>
    ((f i j).sum fun x r => r • A x) - ((f i j).sum fun x r => r * t j x) • (1 : Matrix (Fin n) (Fin n) W)
  let E : Fin a → Matrix (Fin n) (Fin n) W := fun i =>
    ((List.finRange a).map fun j => if j = i then 1 else Z i j).prod
  let Q : Fin a → Matrix (Fin n) (Fin n) W := fun i => E i * P

  have hP : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'),
      ((A ω).map β) *ᵥ v = β ρ • v → (P.map β) *ᵥ v = v := by
    intro R' _ β v hv
    have h := act_smul β v ui (act_add β v hv (act_smul β v (ρ - tr) (act_one β v)))
    rw [h]
    have : β ui * (β ρ + β (ρ - tr) * 1) = β (ui * (2 * ρ - tr)) := by
      simp only [map_mul, map_sub, map_ofNat, _root_.mul_one]; ring
    rw [this, hui, map_one, one_smul]

  have hE : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((E i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have hZ : ∀ j, ((if j = i then 1 else Z i j).map β) *ᵥ v =
        (if j = i then 1 else β ((f i j).sum fun x r => r * t k x) - β ((f i j).sum fun x r => r * t j x)) • v := by
      intro j
      split_ifs
      · exact act_one β v
      · have h1 := act_finsupp β v (fun x => A x) (fun x => β (t k x)) hv (f i j)
        have h2 := act_sub β v h1 (act_smul β v ((f i j).sum fun x r => r * t j x) (act_one β v))
        refine h2.trans ?_
        congr 1
        simp [Finsupp.sum, map_sum, map_mul]
    rw [act_list β v _ _ hZ]
    by_cases hki : k = i
    · rw [if_pos hki]
      subst hki
      refine congrArg (· • v) ?_
      apply List.prod_eq_one
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      split_ifs with hj
      · rfl
      · rw [← map_sub, hf k j (Ne.symm hj), map_one]
    · rw [if_neg hki]
      refine congrArg (· • v) ?_
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩
      rw [if_neg hki, sub_self]
  have hQ : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((Q i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have h1 : (P.map β) *ᵥ v = (1 : R') • v := by
      rw [one_smul]; exact hP R' β v (by rw [hv, htω])
    have h2 := hE R' β k i v hv
    have h3 := act_mul β v h2 h1
    rw [_root_.mul_one] at h3
    exact h3

  have hAP : A ω * P = ρ • P := by
    have hω' : ω * ω = (tr : O) * ω - (nm : O) := by linear_combination hω
    have hA2 : A ω * A ω = (tr : W) • A ω - (nm : W) • (1 : Matrix (Fin n) (Fin n) W) := by
      rw [← map_mul, hω', map_sub, map_mul, map_intCast, map_intCast]
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, zsmul_one, ← zsmul_eq_mul]
    have hnm : (nm : W) = tr * ρ - ρ ^ 2 := by linear_combination hρ
    rw [hPdef, mul_smul_comm, mul_add, mul_smul_comm, _root_.mul_one, hA2, hnm]
    module

  set βL := algebraMap W L
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) W => M.map βL :=
    Matrix.map_injective (IsFractionRing.injective W L)
  have hdec : ∀ x : Fin n → L, ∃ w : Fin a → Fin n → L,
      (∀ i, ((Q i).map βL) *ᵥ x = w i) ∧ (∀ i c, ((A c).map βL) *ᵥ w i = βL (t i c) • w i) ∧
      (P.map βL) *ᵥ x = ∑ i, w i := by
    intro x
    have hy : ((A ω).map βL) *ᵥ ((P.map βL) *ᵥ x) = βL ρ • ((P.map βL) *ᵥ x) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, hAP]
      have : (ρ • P).map βL = βL ρ • P.map βL := by ext; simp
      rw [this, Matrix.smul_mulVec]
    obtain ⟨w, hw, hsum⟩ := hsplit _ hy
    refine ⟨w, fun i => ?_, hw, hsum⟩
    show ((E i * P).map βL) *ᵥ x = w i
    rw [Matrix.map_mul, ← mulVec_mulVec, hsum, mulVec_sum]
    rw [Finset.sum_eq_single i]
    · rw [hE L βL i i (w i) (hw i), if_pos rfl, one_smul]
    · intro k _ hk; rw [hE L βL k i (w k) (hw k), if_neg hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  choose w hwQ hwA hwP using hdec
  have hsumQ : ∑ i, Q i = P := by
    apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [hwP x]
    have : (∑ i, Q i).map βL = ∑ i, (Q i).map βL := by ext; simp [Matrix.sum_apply]
    rw [this, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => hwQ x i
  refine ⟨Q, fun i => ?_, fun i c => ?_, ?_, ?_⟩
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hQ L βL i i _ (hwA x i), if_pos rfl, one_smul]
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    have : (t i c • Q i).map βL = βL (t i c) • (Q i).map βL := by ext; simp
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hwA x i c, this, Matrix.smul_mulVec, hwQ x i]
  · intro R' _ β v hv
    have : (∑ i, Q i).map β = ∑ i, (Q i).map β := by ext; simp [Matrix.sum_apply]
    rw [← Matrix.sum_mulVec, ← this, hsumQ, hP R' β v hv]
  · intro R' _ β i v hv
    rw [hQ R' β i i v hv, if_pos rfl, one_smul]

end GlobalTheory.LieExtProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqToUnitCompOfConstOnFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FibreConstTorus

theorem toUnit_left {S : Scheme.{0}} (G : Over S) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (f ≫ g).appTop a = f.appTop (g.appTop a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

end FibreConstTorus

open FibreConstTorus in

theorem eq_toUnit_comp_of_const_on_fibres : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj B], IsAbelianScheme B → ∀ q : G ⟶ B, Flat q.left → Surjective q.left → QuasiCompact q.left → ∀ (X : Type) [AddCommGroup X] (d : G ⟶ splitTorus S X), (∀ (Z : Over S) (x y : Z ⟶ G), x ≫ q = y ≫ q → x ≫ d = y ≫ d) → ∃ a : 𝟙_ (Over S) ⟶ splitTorus S X, d = toUnit G ≫ a := by
  intro S G B _ hB q hfl hsu hqc X _ d hd
  have hE : EffectiveEpi q.left := inferInstance
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  have hbij : Function.Bijective B.hom.appTop.hom := globalFns_holds S B hB

  have hpb := IsPullback.of_hasPullback q.left q.left
  let Z : Over S := Over.mk (pullback.fst q.left q.left ≫ G.hom)
  let x : Z ⟶ G := Over.homMk (pullback.fst q.left q.left) rfl
  let y : Z ⟶ G := Over.homMk (pullback.snd q.left q.left) (by
    change pullback.snd q.left q.left ≫ G.hom = pullback.fst q.left q.left ≫ G.hom
    rw [← hq, pullback.condition_assoc])
  have hxy : x ≫ q = y ≫ q := by
    ext1
    exact (pullback.condition (f := q.left) (g := q.left))
  have hdl : pullback.fst q.left q.left ≫ d.left = pullback.snd q.left q.left ≫ d.left :=
    congrArg CommaMorphism.left (hd Z x y hxy)
  have key : ∀ c : Γ((splitTorus S X).left, ⊤),
      (pullback.fst q.left q.left).appTop (d.left.appTop c) =
        (pullback.snd q.left q.left).appTop (d.left.appTop c) := fun c => by
    rw [← appTop_comp_apply, ← appTop_comp_apply, hdl]

  obtain ⟨f, hf⟩ : ∃ f, f = splitTorusPointsEquiv S X G d := ⟨_, rfl⟩
  have hfv : ∀ χ : X, (f (Multiplicative.ofAdd χ)).val = d.left.appTop (charUnit S X χ).val :=
    fun χ => hf ▸ splitTorusPointsEquiv_val S X G d χ
  let incl : Γ(S, ⊤)ˣ →* Γ(G.left, ⊤)ˣ := Units.map G.hom.appTop.hom.toMonoidHom
  have hinclv : ∀ u, (incl u).val = G.hom.appTop u.val := fun u => rfl
  have hinj : Function.Injective incl := by
    intro u u' h
    apply Units.ext
    apply hbij.1
    apply FlatDescent.injective_appTop_of_epi q.left
    have h' := congrArg Units.val h
    rw [hinclv, hinclv, ← hq, appTop_comp_apply, appTop_comp_apply] at h'
    exact h'
  have hrange : ∀ m, f m ∈ incl.range := by
    intro m
    obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
    obtain ⟨v, hv, -⟩ := (FlatDescent.existsUnique_units_appTop_eq_iff q.left hpb
      (f (Multiplicative.ofAdd χ))).2 (by
        apply Units.ext
        rw [Units.coe_map, Units.coe_map]
        change (pullback.fst q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val =
          (pullback.snd q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val
        rw [hfv]
        exact key _)
    let e := RingEquiv.ofBijective B.hom.appTop.hom hbij
    refine ⟨Units.map e.symm.toMonoidHom v, Units.ext ?_⟩
    rw [← hv, hinclv]
    change G.hom.appTop (e.symm v.val) = q.left.appTop v.val
    rw [← hq, appTop_comp_apply]
    congr 1
    exact e.apply_symm_apply v.val
  let φ : Multiplicative X →* Γ(S, ⊤)ˣ :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (f.codRestrict incl.range hrange)
  have hφ : ∀ m, incl (φ m) = f m := by
    intro m
    have h2 := MonoidHom.ofInjective_apply hinj (x := (MonoidHom.ofInjective hinj).symm ⟨f m, hrange m⟩)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  refine ⟨(splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ, ?_⟩
  apply (splitTorusPointsEquiv S X G).injective
  refine MonoidHom.ext fun m => Units.ext ?_
  obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
  have h3 := splitTorusPointsEquiv_val S X (𝟙_ (Over S))
    ((splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ) χ
  rw [MulEquiv.apply_symm_apply] at h3
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, toUnit_left,
    appTop_comp_apply, ← h3, ← hinclv, hφ, hfv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianStaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.loc_glob_classes
  | exact GlobalTheory.EtC.loc_glob_classes
  | (intros; apply GlobalTheory.EtC.loc_glob_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrix
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PosOpen

theorem hermForm_smul_real {g : ℕ} (N : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z : Fin g → ℂ) :
    hermForm N ((r : ℂ) • z) ((r : ℂ) • z) = ((r * r : ℝ) : ℂ) * hermForm N z z := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]
  ring

theorem posopen : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) →
    ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  intro g M₀ hM
  have cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C :=
    continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)
  have cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star :=
    continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))
  have dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det := cA.matrix_det
  have dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det := cB.matrix_det
  have dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0 := by simp
  have dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0 := by simp
  have e1 := dA.continuousAt.eventually_ne dA0
  have e2 := dB.continuousAt.eventually_ne dB0

  have cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0 := by
    have h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) =
        fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate) := by
      funext C
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    refine continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)
  have cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))
  have tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1,
      0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re := by
    refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
        (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y) := by
      have : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
          (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y) :=
        (ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
          (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv
          continuousAt_fst).prodMk continuousAt_snd
      exact ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
        (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re)
        (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2))
        cH.continuousAt this
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re := by
      simpa using hM y hy0
    exact cF.eventually (lt_mem_nhds v0)
  filter_upwards [e1, e2, tube] with C h1 h2 h3
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := h3 _ hu
  rw [hermForm_smul_real, Complex.re_ofReal_mul] at this
  exact pos_of_mul_pos_right this (by positivity)

end GlobalTheory.PosOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_quotient_by_finite_translations : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  first | exact @GlobalTheory.TranslQuotient.exists_quotient | exact GlobalTheory.TranslQuotient.exists_quotient | (intros; apply GlobalTheory.TranslQuotient.exists_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem mul_inv_axis_comm_identity {G : Type*} [CommGroup G] (a b W R₁ R₂ : G) :
    a * b⁻¹ * W * (b * R₁) * (a * R₂)⁻¹ = W * R₁ * R₂⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem axis_unit : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'),
    e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen →
    ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen →
    ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
      e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  intro A₀ A₀' X X' ψ e e' π h Q₁ Q₂ hQ₁ hQ₂ w hw ρ₁ ρ₂ hρ₁ hρ₂
  have hpt : ∀ x : A₀, π (e x) = e' (ψ x) := fun x => by
    have := congrArg (fun f : A₀ ⟶ X' => f x) h
    simpa using this
  set D := LB.div (Q₂.pull π) (Q₁.pull π)
  let W : D.ι → A₀.Opens := fun k => e ⁻¹ᵁ D.U k
  have h₁ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₁.pull e').U k.2 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).2
    rw [hpt] at hb
    exact mem_pull.2 hb
  have h₂ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₂.pull e').U k.1 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).1
    rw [hpt] at hb
    exact mem_pull.2 hb
  let u : ∀ k, Γ(A₀, W k)ˣ := fun k =>
    pullU e _ (w.s k) * res (h₁ k) (pullU ψ _ (ρ₁.s k.2)) * (res (h₂ k) (pullU ψ _ (ρ₂.s k.1)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : D.ι) (hz : r z ∈ W k),
      gm r z (W k) (u k) = gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) * (gm (r ≫ ψ) z _ (ρ₂.s k.1))⁻¹ := by
    intro Z r z k hz
    simp only [u, map_mul, map_inv]
    rw [gm_res r z (h₁ k) hz, gm_res r z (h₂ k) hz, gm_pull r e z _ hz, gm_pull r ψ z _ (h₁ k hz),
      gm_pull r ψ z _ (h₂ k hz)]
  have hcov : (⊤ : A₀.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π (e x))
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π (e x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((fun _ => i), (fun _ => j)), mem_divPull.2 ⟨hi, hj⟩⟩
  have hcomp : ∀ k l, ∀ x ∈ W k ⊓ W l, gm (𝟙 A₀) x (W k) (u k) = gm (𝟙 A₀) x (W l) (u l) := by
    intro k l x hx
    rw [hu _ _ x k hx.1, hu _ _ x l hx.2]
    simp only [Category.id_comp]
    have hk : e x ∈ D.U k := hx.1
    have hl : e x ∈ D.U l := hx.2
    have hk' := mem_divPull.1 hk
    have hl' := mem_divPull.1 hl
    have hk₁ : ψ x ∈ (Q₁.pull e').U k.2 := h₁ k hx.1
    have hl₁ : ψ x ∈ (Q₁.pull e').U l.2 := h₁ l hx.2
    have hk₂ : ψ x ∈ (Q₂.pull e').U k.1 := h₂ k hx.1
    have hl₂ : ψ x ∈ (Q₂.pull e').U l.1 := h₂ l hx.2
    have E := gen_germ hw e x hk hl
    rw [germ_div_g _ _ e x hk hl] at E
    rw [show e = 𝟙 A₀ ≫ e from (Category.id_comp e).symm] at E
    rw [gm_pull_g Q₂ π (𝟙 A₀ ≫ e) x hk'.1 hl'.1, gm_pull_g Q₁ π (𝟙 A₀ ≫ e) x hk'.2 hl'.2] at E
    simp only [Category.id_comp] at E
    have R₁ := gen_germ hρ₁ ψ x hk₁ hl₁
    have R₂ := gen_germ hρ₂ ψ x hk₂ hl₂
    rw [show ψ = 𝟙 A₀ ≫ ψ from (Category.id_comp ψ).symm] at R₁ R₂
    rw [gm_pull_g Q₁ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₁) (mem_pull.1 hl₁)] at R₁
    rw [gm_pull_g Q₂ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₂) (mem_pull.1 hl₂)] at R₂
    simp only [Category.id_comp, ← h] at E R₁ R₂
    rw [E, R₁, R₂]
    exact mul_inv_axis_comm_identity _ _ _ _ _
  obtain ⟨g, hg⟩ := glue_unit (⊤ : A₀.Opens) W (fun _ => le_top) hcov u hcomp
  refine ⟨g, fun Z r z k hk => ?_⟩
  have hz : r z ∈ W k := hk
  have e₁ : gm r z ⊤ g = gm r z (W k) (u k) := by rw [← hg k, gm_res r z le_top hz]
  rw [e₁, hu Z r z k hz, inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyAStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_stabiliserLog_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | exact GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | (intros; apply GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family <;> assumption)
end

