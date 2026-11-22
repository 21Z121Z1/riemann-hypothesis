import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0007
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorOnRayOfLinIndepSubcell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace CellRay

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m' : ℕ}

theorem inCell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

end CellRay

end GlobalTheory.PolFan

open GlobalTheory.PolFan.CellRay in

theorem GlobalTheory.PolFan.cell_gen_on_ray : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X)
    (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  intro O _ bar φ X _ _ _ m n δ γ c hδ hγ hli hc hrel i
  classical

  obtain ⟨k, d, hk, hkd⟩ := inCell hγ hδ.mem hδ.nonneg (a := fun _ => (1 : ℝ)) (b := c) (fun _ => zero_le_one) hc
    ((linearOn_iff φ δ).1 hδ.linear (fun _ => 1) fun _ => zero_le_one) (by simpa using hrel) i one_ne_zero

  have hB : ∀ j, ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ (d j ≠ 0 → kj • γ j = ∑ l, e l • δ l) := by
    intro j
    by_cases hd : d j = 0
    · exact ⟨1, 0, one_pos, fun h => absurd hd h⟩
    obtain ⟨kj, e, hkj, he⟩ := inCell (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hδ hγ.mem hγ.nonneg
      (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
      ((linearOn_iff φ γ).1 hγ.linear _ fun j => Nat.cast_nonneg _) (by
        refine LinearMap.ext₂ fun a b => ?_
        have := LinearMap.congr_fun₂ hkd a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
        simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
        exact_mod_cast this.symm) j (by exact_mod_cast hd)
    exact ⟨kj, e, hkj, fun _ => he⟩
  choose kk e hkk he using hB
  set K := ∏ j, kk j with hKdef
  let Kj : Fin n → ℕ := fun j => ∏ j' ∈ Finset.univ.erase j, kk j'
  have hK : ∀ j, kk j * Kj j = K := fun j => Finset.mul_prod_erase Finset.univ kk (Finset.mem_univ j)
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hkk j
  have hKj : ∀ j, Kj j ≠ 0 := fun j h => by
    have := hK j
    rw [h, mul_zero] at this
    omega
  have hterm : ∀ j, (K * d j) • γ j = ∑ l, (d j * Kj j * e j l) • δ l := by
    intro j
    by_cases hd : d j = 0
    · simp [hd]
    rw [← hK j, show kk j * Kj j * d j = (d j * Kj j) * kk j by ring, ← smul_smul, he j hd, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have key : (K * k) • δ i = ∑ l, (∑ j, d j * Kj j * e j l) • δ l := by
    rw [← smul_smul, hkd, Finset.smul_sum]
    simp only [smul_smul, hterm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
  have hFG := Fintype.linearIndependent_iffₛ.1 hli (fun l => ((∑ j, d j * Kj j * e j l : ℕ) : ℤ))
    (fun l => if l = i then ((K * k : ℕ) : ℤ) else 0) (by
      simp only [Nat.cast_smul_eq_nsmul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact key.symm)
  have hoff : ∀ l, l ≠ i → ∀ j, d j * Kj j * e j l = 0 := by
    intro l hl j
    have := hFG l
    simp only [if_neg hl, Nat.cast_eq_zero] at this
    exact (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ _)
  have hon : ∑ j, d j * Kj j * e j i ≠ 0 := by
    have := hFG i
    rw [if_pos rfl, Nat.cast_inj] at this
    rw [this]
    exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hon
  have hdj : d j ≠ 0 := fun h => hj (by rw [h]; ring)
  have hej : e j i ≠ 0 := fun h => hj (by rw [h]; ring)
  have hel : ∀ l, l ≠ i → e j l = 0 := fun l hl => by
    have := hoff l hl j
    rcases Nat.mul_eq_zero.1 this with h | h
    · rcases Nat.mul_eq_zero.1 h with h' | h'
      · exact absurd h' hdj
      · exact absurd h' (hKj j)
    · exact h
  have hγj : kk j • γ j = e j i • δ i := by
    rw [he j hdj, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  exact ⟨j, e j i, kk j, Nat.pos_of_ne_zero hej, hkk j, hγj.symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramifiedStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_formally_unramified : ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A] (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  first | exact @GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion | exact GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion | (intros; apply GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
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
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem exists_generisation_height_one : ∀ (X : Scheme.{0}) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (q : Ideal (X.presheaf.stalk (ξ (closedPoint R)))) [q.IsPrime], q.height = 1 → ∃ (z : X) (hs : z ⤳ ξ (closedPoint R)), ringKrullDim (X.presheaf.stalk z) = 1 ∧ q.map (X.presheaf.stalkSpecializes hs).hom = maximalIdeal (X.presheaf.stalk z) ∧ ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), (maximalIdeal W).comap (g.comp (Scheme.stalkClosedPointTo ξ).hom) = q → (spMap g ≫ ξ) (closedPoint W) = z := by
  intro X R _ _ ξ q _ hq
  let y : PrimeSpectrum (X.presheaf.stalk (ξ (closedPoint R))) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := stalk_fromSpecStalk_equiv X (ξ (closedPoint R)) q
  have hs : X.fromSpecStalk (ξ (closedPoint R)) y ⤳ ξ (closedPoint R) := by
    have : X.fromSpecStalk (ξ (closedPoint R)) y ∈ Set.range (X.fromSpecStalk (ξ (closedPoint R))) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk (ξ (closedPoint R))) (Localization.AtPrime q)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime q) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  have hf : (X.presheaf.stalkSpecializes hs).hom = e.symm.toRingHom.comp (algebraMap _ (Localization.AtPrime q)) := by
    ext a
    have h5 : e ((X.presheaf.stalkSpecializes hs).hom a) =
        algebraMap _ (Localization.AtPrime q) a := congrArg (fun f => f.hom a) hcomp
    change _ = e.symm (algebraMap _ (Localization.AtPrime q) a)
    rw [← h5, e.symm_apply_apply]
  refine ⟨X.fromSpecStalk (ξ (closedPoint R)) y, hs, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  · rw [hf, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    have : (Ideal.map e.symm.toRingHom (maximalIdeal (Localization.AtPrime q))).IsMaximal :=
      Ideal.map_isMaximal_of_equiv e.symm
    exact IsLocalRing.eq_maximalIdeal this
  · intro W _ _ g hg
    have h4 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h6 : (Spec.map (Scheme.stalkClosedPointTo ξ)) ((spMap g) (closedPoint W)) = y := by
      apply PrimeSpectrum.ext
      change _ = q
      rw [← hg]
      rfl
    have h7 : (spMap g ≫ ξ) (closedPoint W) = X.fromSpecStalk (ξ (closedPoint R))
        ((Spec.map (Scheme.stalkClosedPointTo ξ)) ((spMap g) (closedPoint W))) := by
      conv_lhs => rw [← h4]
      rfl
    rw [h7, h6]

end GlobalTheory.LocalRingGeneralisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowLSOfNotDvd
section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Subst

variable {R : Type} [CommRing R] {a : ℕ} (ha : 1 ≤ a)

def powPS : PowerSeries R →+* PowerSeries R := (PowerSeries.expand a (by omega)).toRingHom

theorem powPS_apply (g : PowerSeries R) : powPS ha g = PowerSeries.expand a (by omega) g := rfl

theorem powPS_comp_C : (powPS ha).comp (PowerSeries.C (R := R)) = PowerSeries.C :=
  RingHom.ext fun r => PowerSeries.expand_C a (by omega) r

theorem powPS_X : powPS ha (PowerSeries.X : PowerSeries R) = PowerSeries.X ^ a := PowerSeries.expand_X a (by omega)

theorem powPS_injective : Function.Injective (powPS ha : PowerSeries R → PowerSeries R) := fun f g h => by
  ext m
  have := congrArg (PowerSeries.coeff (a * m)) h
  simpa only [powPS_apply, PowerSeries.coeff_expand_mul] using this

theorem map_powPS {S : Type} [CommRing S] (f : R →+* S) (g : PowerSeries R) :
    PowerSeries.map f (powPS ha g) = powPS ha (PowerSeries.map f g) := PowerSeries.map_expand a (by omega) f g

variable {K : Type} [Field K]

def powLS : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (a : ℤ)) (mul_right_injective₀ (Int.natCast_ne_zero.2 (by omega)))
    fun _ _ => mul_le_mul_iff_right₀ (Int.natCast_pos.2 (by omega))

theorem coeff_powLS_mul (f : LaurentSeries K) (n : ℤ) : (powLS ha f).coeff (a * n) = f.coeff n :=
  HahnSeries.embDomain_coeff

theorem coeff_powLS_of_not_dvd (f : LaurentSeries K) {n : ℤ} (h : ¬ (a : ℤ) ∣ n) : (powLS ha f).coeff n = 0 :=
  HahnSeries.embDomain_of_notMem_range fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩

theorem powLS_coe (g : PowerSeries K) :
    powLS ha (HahnSeries.ofPowerSeries ℤ K g) = HahnSeries.ofPowerSeries ℤ K (powPS ha g) := by
  ext n
  by_cases h : (a : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_powLS_mul]
    have ha' : (0 : ℤ) < a := Int.natCast_pos.2 (by omega)
    rcases lt_or_ge m 0 with hm | hm
    · simp [PowerSeries.coeff_coe, hm, mul_neg_of_pos_of_neg ha' hm]
    · lift m to ℕ using hm
      rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries, powPS_apply,
        PowerSeries.coeff_expand_mul]
  · rw [coeff_powLS_of_not_dvd ha _ h, PowerSeries.coeff_coe]
    split_ifs
    · rfl
    · exact (PowerSeries.coeff_expand_of_not_dvd a (by omega) g fun h' => h (Int.natCast_dvd.2 h')).symm

theorem powLS_comp_toLaurent {p : ℕ} (F : DVF p) : (powLS ha).comp F.toLaurent = F.toLaurent.comp (powPS ha) := by
  refine RingHom.ext fun g => ?_
  show powLS ha (HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map _ g)) =
    HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map _ (powPS ha g))
  rw [powLS_coe, map_powPS]

end Subst

theorem dualMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem coe_nsmul_apply {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (n : ℕ) (γ : levelForms H N X) (y z : X) :
    ((n • γ : levelForms H N X) : LinearMap.BilinForm ℤ X) y z = n * (γ : LinearMap.BilinForm ℤ X) y z := by
  simp

theorem pow_zpow_form {F : Type} [Field F] (uF : F) (n : ℕ) {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (γ : levelForms H N X) (y z : X) {k : ℤ} (hk : k ∣ (γ : LinearMap.BilinForm ℤ X) y z) :
    uF ^ (((n • γ : levelForms H N X) : LinearMap.BilinForm ℤ X) y z / k) =
      (uF ^ n) ^ ((γ : LinearMap.BilinForm ℤ X) y z / k) := by
  rw [coe_nsmul_apply, Int.mul_ediv_assoc _ hk, zpow_mul, zpow_natCast]

theorem smul_mem_adm {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {γ : levelForms H N X}
    (h : γ ∈ admitted H N X) {n : ℕ} (hn : 1 ≤ n) : n • γ ∈ admitted H N X := by
  refine ⟨fun y hy => ?_, fun y z => ?_⟩
  · rw [coe_nsmul_apply]
    exact mul_pos (by exact_mod_cast hn) (h.1 y hy)
  · rw [coe_nsmul_apply]
    exact Dvd.dvd.mul_left (h.2 y z) _

section Reform

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a₀ : ArcIn Dw l β A b}

def reform {γ : levelForms H l.M' a₀.D₀.X} {h : γ ∈ admitted H l.M' a₀.D₀.X} {n : ℕ} (h' : n • γ ∈ admitted H l.M' a₀.D₀.X)
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f f' : A →+* R} {u u' : R} {χ : Sp R ⟶ Y.X}
    (W : ArcWit Y (withForm a₀ γ h) I f u' χ) (hf : f = f') (hu : u' = u ^ n) :
    ArcWit Y (withForm a₀ (n • γ) h') I f' u χ where
  t := W.t
  m := W.m
  P := W.P
  φ := W.φ
  he := hf ▸ W.he
  w := W.w
  e := W.e
  spec := by
    subst hf hu
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
    refine ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF hF hu => ?_⟩
    obtain ⟨k1, k2⟩ := s6 F (uF ^ n) hF (by rw [hu, map_pow, map_pow])
    have dv : ∀ y z, (2 * (l.M' : ℤ)) ∣ (γ : LinearMap.BilinForm ℤ a₀.D₀.X) y z := h.2
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => k2 yF hyF k p₀ σ hσ q₀ q x e1 e2 (fun z => ?_) e4⟩
    · have e := pow_zpow_form uF n γ y y (k := 2) ((dvd_mul_right 2 _).trans (dv y y))
      change GenRel _ _ _ (uF ^ (((n • γ : levelForms H l.M' a₀.D₀.X) : LinearMap.BilinForm ℤ a₀.D₀.X) y y / 2))
      rw [e]
      exact k1 y
    · have hk : (k : ℤ) ∣ 2 * (l.M' : ℤ) := by
        refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 ?_) _
        rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Nat.dvd_lcm_right l.M l.A
        · exact Nat.dvd_lcm_left l.M l.A
      have e := pow_zpow_form uF n γ q₀.y z (k := k) (hk.trans (dv _ _))
      have e3 := e3 z
      change GenRel _ _ _ (uF ^ (((n • γ : levelForms H l.M' a₀.D₀.X) : LinearMap.BilinForm ℤ a₀.D₀.X) q₀.y z / k)) at e3
      rw [e] at e3
      exact e3

end Reform

theorem isArcChart_pow {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a₀ a₁ : ArcIn Dw l β A b} {ϖ : A}
    {χ : Sp (PowerSeries A) ⟶ Y.X} {a : ℕ} (ha : 1 ≤ a) (hχ : IsArcChart Y a₀ ϖ χ)
    (hW : Nonempty (Wit Y a₁ (spMap (powPS ha) ≫ χ))) : IsArcChart Y a₁ ϖ (spMap (powPS ha) ≫ χ) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := hχ
  have mem : ∀ (x : Sp (PowerSeries A)) (s : PowerSeries A),
      s ∈ (spMap (powPS (R := A) ha) x).asIdeal ↔ powPS ha s ∈ x.asIdeal := fun _ _ => Iff.rfl
  have ev : ∀ x, (spMap (powPS (R := A) ha) ≫ χ) x = χ (spMap (powPS (R := A) ha) x) := fun _ => rfl
  refine ⟨?_, fun x => ?_, fun x hx => ?_, (Y.hasArcData_iff _ _ _ _ _).2 hW⟩
  · rw [Category.assoc, h₁, ← Category.assoc, ← spMap_comp, powPS_comp_C]
  · rw [ev]
    refine (h₂ (spMap (powPS (R := A) ha) x)).trans ?_
    rw [mem, powPS_X]
    exact not_congr ⟨fun h => x.isPrime.mem_of_pow_mem a h, fun h => Ideal.pow_mem_of_mem _ h a (by omega)⟩
  · rw [ev]
    refine h₃ (spMap (powPS (R := A) ha) x) fun hm => hx ?_
    rw [mem, map_mul, powPS_X, ← RingHom.comp_apply, powPS_comp_C] at hm
    rcases x.isPrime.mem_or_mem hm with hm | hm
    · exact Ideal.mul_mem_right _ _ hm
    · exact Ideal.mul_mem_left _ _ (x.isPrime.mem_of_pow_mem a hm)

theorem exists_lift_bc {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {G : Over (Sp R)} {G' : Over (Sp R')}
    (bc : G' ≅ (Over.pullback (Out.specOf g)).obj G) (w : epsR R ⟶ G) :
    ∃ v : epsR R' ⟶ G', v.left ≫ bc.hom.left ≫ pullback.fst G.hom (Out.specOf g) = spMap (dualMap g) ≫ w.left := by
  have cond : (spMap (dualMap g) ≫ w.left) ≫ G.hom = (epsR R').hom ≫ Out.specOf g := by
    rw [Category.assoc, Over.w w]
    exact GlobalTheory.ArcCompare.dual_over g
  refine ⟨Over.homMk (pullback.lift _ _ cond ≫ bc.inv.left) ?_, ?_⟩
  · rw [Category.assoc, Over.w bc.inv]
    exact pullback.lift_snd _ _ _
  · simp only [Over.homMk_left]
    rw [Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
    exact pullback.lift_fst _ _ _

theorem flagAt_bc {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (Z : Mdl Y i₀) {k k' : Type} [Field k] [Field k'] (s : k →+* k') {x : Sp k ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x v) : Z.FlagAt (spMap s ≫ x) (v.bc s) := by
  obtain ⟨a, φ, e, hfr, hfl⟩ := h
  refine ⟨a, s.comp φ, ?_, ?_, ?_⟩
  · rw [← e, spMap_comp, Category.assoc]
  · have := GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ s _ _ hfr
    rw [Category.assoc]
    exact this
  · have := GlobalTheory.DRFlag.Spez.sameFlag_bc s hfl
    rw [Vecs.bc_bc] at this
    rwa [Category.assoc]

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

theorem IsArc.pow {a : ℕ} (ha : 1 ≤ a) {γ : t.Forms} {x : Sp (LaurentSeries ↥F.K) ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K)} (hx : IsArc t γ x v) :
    IsArc t (a • γ) (spMap (powLS ha) ≫ x) (v.bc (powLS ha)) := by
  obtain ⟨h, ϖ, χ, Wt, w, hϖ, hχ, hw, hxχ, hv, hfl⟩ := hx
  have h' : a • γ ∈ t.Dir := smul_mem_adm h ha
  have hI : (Ideal.span {(PowerSeries.X : PowerSeries F.O)}).map (powPS (R := F.O) ha) ≤ Ideal.span {PowerSeries.X} := by
    rw [Ideal.map_span, Set.image_singleton, powPS_X]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (by omega))
  obtain ⟨W₁, hD, bc, -, hU, hm, he, w₁, hφ, hw₁, T⟩ := ArcWit.baseChange GlobalTheory.allSixLaws.2.2.1.cubePull GlobalTheory.polBaseChange_holds
    GlobalTheory.UnifPullGuards.unifBaseChange_holds GlobalTheory.allSixLaws.2.2.2.2.1 (qkPullExists GlobalTheory.globalFns_holds) polOActPull
    (GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X F.O) (GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X F.O) Wt (powPS (R := F.O) ha) (powPS_injective ha) hI
  let W' : Wit (Y Z.i) (withForm t.a (a • γ) h') (spMap (powPS (R := F.O) ha) ≫ χ) :=
    reform (f' := PowerSeries.C) (u := PowerSeries.X) h' W₁ (powPS_comp_C ha) (powPS_X ha)
  choose w' hw' using fun τ k => exists_lift_bc (R := PowerSeries F.O) (R' := PowerSeries F.O) (G := Wt.t.G) (G' := W₁.t.G) (powPS (R := F.O) ha) bc (w τ k)
  have hX : powPS (R := F.O) ha (PowerSeries.X : PowerSeries F.O) ∈ Ideal.span {PowerSeries.X} := hI (Ideal.mem_map_of_mem _
    (Ideal.mem_span_singleton_self _))
  refine ⟨h', ϖ, spMap (powPS (R := F.O) ha) ≫ χ, W', w', hϖ, isArcChart_pow ha hχ ⟨W'⟩, fun τ k => ?_, ?_, fun τ k => ?_,
    flagAt_bc Z _ hfl⟩
  · exact GlobalTheory.T.admissible_forms_arc_compare E H Dw _ _ _ _ _ (Y Z.i) F.O _ t.a γ (a • γ) h h' χ (powPS (R := F.O) ha) Wt W' hD bc w₁
      (powPS_comp_C ha) hX hU he hφ hw₁ T (t.e τ k) (w τ k) (w' τ k) (hw τ k) (hw' τ k)
  · rw [Category.assoc, hxχ, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, powLS_comp_toLaurent]
  · change spMap (dualMap (powLS ha)) ≫ v τ k = spMap (dualMap F.toLaurent) ≫ (w' τ k).left ≫ W₁.m.φ
    rw [hv, hm]
    simp only [Category.assoc]
    rw [reassoc_of% (hw' τ k), ← Category.assoc, ← Category.assoc (spMap (dualMap F.toLaurent)), ← spMap_comp,
      ← spMap_comp, ← dualMap_comp, ← dualMap_comp, powLS_comp_toLaurent]

end GlobalTheory.LocM.FJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCountStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coisotropic_sublattice_of_torsion_count : ∀ (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ), M.det ≠ 0 → LinearIndependent ℚ (fun i j => (A i j : ℚ)) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i)) → ∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  first | exact @GlobalTheory.CoisoCount.coisotropic_of_torsion_count | exact GlobalTheory.CoisoCount.coisotropic_of_torsion_count | (intros; apply GlobalTheory.CoisoCount.coisotropic_of_torsion_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteHolomorphicCoordinatesIndependentDiffereStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_holomorphic_coordinates_independent_differentials : ∀ (n a : ℕ) (v₀ : ReciprocityTheory.L2DbarEstimates.V n) (O : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ), IsOpen O → v₀ ∈ O → (∀ i, DifferentiableOn ℂ (G i) O) → (∀ i, G i v₀ = 0) → LinearIndependent ℂ (fun i => fderiv ℂ (G i) v₀) → ∃ ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ), v₀ ∈ ψ.source ∧ ψ.source ⊆ O ∧ ψ v₀ = 0 ∧ DifferentiableOn ℂ ψ ψ.source ∧ DifferentiableOn ℂ ψ.symm ψ.target ∧ ∀ v ∈ ψ.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), ψ v j = G ⟨j, hj⟩ v := by
  first | exact @GlobalTheory.CompleteCoords.complete_coords | exact GlobalTheory.CompleteCoords.complete_coords | (intros; apply GlobalTheory.CompleteCoords.complete_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  first | exact @GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | exact GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | (intros; apply GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  first | exact @GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | exact GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | (intros; apply GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDeRhamFlagStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_de_rham_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ Z : Mdl Y i₀, (∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) → ∃ Z', IsDRFlag Z Z' := by
  first | exact @GlobalTheory.DRFlag.exists_isDRFlag | exact GlobalTheory.DRFlag.exists_isDRFlag | (intros; apply GlobalTheory.DRFlag.exists_isDRFlag <;> assumption)
end

