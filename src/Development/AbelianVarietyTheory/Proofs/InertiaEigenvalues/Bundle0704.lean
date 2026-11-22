import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppLatStd

theorem exists_mem_only {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ b ∈ Q.asIdeal ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → b ∈ P → P = Q.asIdeal := by
  have hQ0 : Q.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero Q.ne_bot
  have hH : Fintype.card (ClassGroup (𝓞 E)) ≠ 0 := Fintype.card_ne_zero
  have hp : (Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    refine (ClassGroup.mk0_eq_one_iff (pow_mem hQ0 _)).1 ?_
    have : (⟨Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)), pow_mem hQ0 _⟩ : nonZeroDivisors (Ideal (𝓞 E))) =
        ⟨Q.asIdeal, hQ0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨b, hb⟩ := hp.principal
  have hbm : b ∈ Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) := hb ▸ Submodule.mem_span_singleton_self b
  refine ⟨b, fun h0 => ?_, Ideal.pow_le_self hH hbm, fun P hP hbP => ?_⟩
  · rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at hb
    exact pow_ne_zero _ Q.ne_bot hb
  · have hle : Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) ≤ P := by
      rw [hb]; exact (Ideal.span_singleton_le_iff_mem P).2 hbP
    exact (Q.isMaximal.eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm

theorem val_mul_mulVec_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K)
    (c : K) (hz : ∀ j, Valued.v (z j) ≤ 1) (hM : ∀ i j, Valued.v c * Valued.v (M i j) ≤ 1) (i : Fin n) :
    Valued.v (c * M.mulVec z i) ≤ 1 := by
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul]
  exact mul_le_one' (hM i j) (hz j)

end GlobalTheory.SuppLatStd

namespace GlobalTheory.SuppLatStd

set_option maxHeartbeats 2000000 in

theorem lat_std_of_suppAt : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  intro D V hg hL h e Ps bad he hbad hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e1 : ∀ Q ∈ Ps, ev Q e = 1 := fun Q hQ => by
    rw [hsum, map_sum, Finset.sum_eq_single Q (fun Q' h' hne => (hid _ _ (hes Q' h')).2.2 Q hne.symm)
      (fun h' => absurd hQ h'), (hid _ _ (hes Q hQ)).2.1]
  have e2 : ∀ Q, Q ∉ Ps → ev Q e = 0 := fun Q hQ => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  have hP : ∀ Q ∈ Ps, GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ hQ' => by
    have a := congrArg (ev (GlobalTheory.IdemSupport.cP Q)) horth
    rw [map_mul, e1 _ hQ', one_mul, map_zero] at a
    have a' := hcj e Q
    rw [a, e1 Q hQ, map_zero, map_one] at a'
    exact zero_ne_one a'

  have hA1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h) = 1 := fun Q hQ hQ' => by
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ hQ', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    have hu : ev Q (e + cA D e) = 0 := by rw [map_add, e2 Q hQ, a, add_zero]
    have : (ev Q).mapMatrix (mt V h - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev Q ((mt V h - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ Q, (ev Q).mapMatrix (mt V h) * (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q => by
    rw [← map_mul, show mt V h * mt V h⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q hQ hQ' => by
    have := hinv Q
    rwa [hA1 Q hQ hQ', one_mul] at this

  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  set S := Ps ∪ Ps.image GlobalTheory.IdemSupport.cP with hS
  set f : HeightOneSpectrum (𝓞 D.host.E) × Fin V.rank × Fin V.rank → ℕ := fun p =>
    fn (Valued.v (ev p.1 (mt V h p.2.1 p.2.2))) ⊔ fn (Valued.v (ev p.1 (mt V h⁻¹ p.2.1 p.2.2))) with hf
  set N : ℕ := (S ×ˢ (Finset.univ ×ˢ Finset.univ : Finset (Fin V.rank × Fin V.rank))).sup f with hN'
  have hN : ∀ Q ∈ S, ∀ i j, Valued.v (ev Q (mt V h i j)) ≤ WithZero.exp (N : ℤ) ∧
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ WithZero.exp (N : ℤ) := by
    intro Q hQ i j
    have hle : f (Q, i, j) ≤ N := Finset.le_sup (Finset.mem_product.2 ⟨hQ, Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ j⟩⟩)
    constructor
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_left.trans hle))
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_right.trans hle))
  have hout : ∀ Q, Q ∉ S → Q ∉ Ps ∧ GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ =>
    ⟨fun h' => hQ (Finset.mem_union_left _ h'), fun h' => hQ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP Q⟩))⟩

  choose b hb0 hbQ hbP using fun Q : HeightOneSpectrum (𝓞 D.host.E) => exists_mem_only Q
  set m : 𝓞 D.host.E := (∏ Q ∈ S, b Q) ^ N with hm
  have hm1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ 1 :=
    fun Q => (GlobalTheory.CharLocProd.val_algebraMap Q _).trans_le (Q.valuation_le_one m)
  have hmN : ∀ Q ∈ S, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E)
      (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ WithZero.exp (-(N : ℤ)) := fun Q hQ => by
    rw [GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow ?_ N)
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hQ
    rw [hc]; exact Ideal.mul_mem_right _ _ (hbQ Q)
  have hone : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (i j : Fin V.rank),
      Valued.v ((1 : Matrix (Fin V.rank) (Fin V.rank) K) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hcond : ∀ Q i j, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h i j)) ≤ 1 ∧
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ 1 := fun Q i j => by
    by_cases hQ : Q ∈ S
    · have k : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
        rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      exact ⟨(mul_le_mul' (hmN Q hQ) (hN Q hQ i j).1).trans k.le, (mul_le_mul' (hmN Q hQ) (hN Q hQ i j).2).trans k.le⟩
    · obtain ⟨o1, o2⟩ := hout Q hQ
      have a1 : ev Q (mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hA1 Q o1 o2) i) j
      have a2 : ev Q (mt V h⁻¹ i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hB1 Q o1 o2) i) j
      rw [a1, a2]
      exact ⟨mul_le_one' (hm1 Q) (hone i j), mul_le_one' (hm1 Q) (hone i j)⟩

  have hmat : ∀ Q, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1.map (GlobalTheory.CharLocProd.evalAt Q) =
      (ev Q).mapMatrix (mt V h⁻¹) := fun Q => by
    rw [← map_inv, ← Subgroup.coe_inv, ← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hev]
    rfl
  have memG : ∀ x, x ∈ Bridge.hLat V (finPt V h) ↔ ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((((ev Q).mapMatrix (mt V h⁻¹)).mulVec
      (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i) ≤ 1 := fun x => by
    rw [GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL (finPt V h) x]
    refine forall_congr' fun i => forall_congr' fun Q => ?_
    rw [← hmat Q]
    have := RingHom.map_mulVec (GlobalTheory.CharLocProd.evalAt Q) ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i
    exact iff_of_eq (congrArg (fun w => Valued.v w ≤ 1) this)
  have memS : ∀ x, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (x i)) ≤ 1 := fun x => by
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp only [OneMemClass.coe_one, map_one, inv_one, Units.val_one, Matrix.one_mulVec]
    rfl
  have hsm : ∀ (x : Fin V.rank → D.host.E) i, (m • x) i = algebraMap (𝓞 D.host.E) D.host.E m * x i := fun x i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  refine ⟨m, pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q), ?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memS _).2 fun i Q => ?_)
    have hx' := (memG x).1 hx
    have e3 : algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) i) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) *
          ((ev Q).mapMatrix (mt V h)).mulVec (((ev Q).mapMatrix (mt V h⁻¹)).mulVec
            (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i := by
      rw [Matrix.mulVec_mulVec, hinv Q, Matrix.one_mulVec, hsm, map_mul]
    rw [e3]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).1) i
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memG _).2 fun i Q => ?_)
    have hx' := (memS x).1 hx
    have e3 : (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) j)) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) •
          (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j)) := funext fun j => by
      rw [hsm, map_mul]; rfl
    rw [e3, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).2) i
  · have hmap : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ Q.asIdeal := fun Q hne heq => by
      refine hne (HeightOneSpectrum.ext ?_)
      rw [← heq]
      ext x
      rw [GlobalTheory.IdemSupport.mem_cP]
      have hle : Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤
          Q.asIdeal.comap (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
        Ideal.map_le_iff_le_comap.2 fun y hy => by
          rw [Ideal.mem_comap, Ideal.mem_comap]; simpa [GlobalTheory.IdemSupport.cO_cO] using hy
      constructor
      · intro hx
        simpa [GlobalTheory.IdemSupport.cO_cO] using
          Ideal.mem_map_of_mem (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) hx
      · intro hx
        simpa using hle hx
    intro P hPp hmP
    obtain ⟨Q, hQS, hbQP⟩ := (hPp.prod_mem_iff).1 (hPp.mem_of_pow_mem _ hmP)
    obtain rfl := hbP Q P hPp hbQP
    rcases Finset.mem_union.1 hQS with hQ | hQ
    · exact ⟨hmap Q fun hc => hP Q hQ (by rw [hc]; exact hQ), hbad Q hQ⟩
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
      refine ⟨hmap _ fun hc => hP Q' hQ' ?_, fun hm' => hbad Q' hQ' ?_⟩
      · rw [GlobalTheory.ClassScalarValue.cP_cP] at hc
        rw [← hc]; exact hQ'
      · rwa [GlobalTheory.IdemSupport.mem_cP, map_natCast] at hm'

end GlobalTheory.SuppLatStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semilinear_square_of_basis {A B N N' Q Q' ι : Type} [CommRing A] [CommRing B] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    {c : A →+* B} (β : Module.Basis ι A N) (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q')
    (G : Q →ₗ[B] Q') (h : ∀ k, j' (w (β k)) = G (j (β k))) (x : N) : j' (w x) = G (j x) :=
  LinearMap.congr_fun (β.ext (f₁ := j'.comp w) (f₂ := G.comp j) h) x

theorem sum_smul_column_eq {R B T T' : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup T]
    [Module R T] [AddCommGroup T'] [Module R T'] {d d' : ℕ} (b : Module.Basis (Fin d) R T)
    (b' : Module.Basis (Fin d') R T') (f : T →ₗ[R] T') (U : Matrix (Fin d) (Fin d) B)
    (U' : Matrix (Fin d') (Fin d') B) (Y : Matrix (Fin d') (Fin d) B)
    (h : U' * Y = (LinearMap.toMatrix b b' f).map (algebraMap R B) * U) (k : Fin d) :
    ∑ i, Y i k • ∑ m, U' m i ⊗ₜ[R] b' m = f.baseChange B (∑ i, U i k ⊗ₜ[R] b i) := by
  have h1 : ∀ i, f (b i) = ∑ m, LinearMap.toMatrix b b' f m i • b' m := fun i => by
    conv_lhs => rw [← b'.sum_repr (f (b i))]
    simp only [LinearMap.toMatrix_apply]
  have h2 : ∀ m, ∑ i, Y i k * U' m i = ∑ i, LinearMap.toMatrix b b' f m i • U i k := fun m => by
    have := congrFun (congrFun h m) k
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp only [Algebra.smul_def, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [map_sum, LinearMap.baseChange_tmul, h1, TensorProduct.tmul_sum, Finset.smul_sum,
    TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul, h2]

theorem square_column {S A B P P' N N' Q Q' κ : Type} [CommRing S] [CommRing A] [CommRing B] [AddCommGroup P]
    [Module S P] [AddCommGroup P'] [Module S P'] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    [Fintype κ] {a : S →+* A} {c : A →+* B} (t : P →ₛₗ[a] N) (t' : P' →ₛₗ[a] N') (v : P →ₗ[S] P')
    (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q') (G : Q →ₗ[B] Q') (hw : ∀ x, w (t x) = t' (v x))
    {n : N} {p : P} {y : κ → S} {e : κ → P'} {q : Q} {q' : κ → Q'} (hn : n = t p) (hp : v p = ∑ i, y i • e i)
    (hq : j (t p) = q) (hq' : ∀ i, j' (t' (e i)) = q' i) (h : ∑ i, c (a (y i)) • q' i = G q) :
    j' (w n) = G (j n) := by
  rw [hn, hw, hp, hq, ← h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [t'.map_smulₛₗ, j'.map_smulₛₗ, hq']

theorem exists_fHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  intro l _ K T _ _ ρ T' _ _ ρ' M M' j j' H H' f hf
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨d, S, e, hS⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M
  obtain ⟨d', S', e', hS'⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M'
  obtain ⟨b, U, hU, hj⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d S M e hS T ρ j H
  obtain ⟨b', U', hU', hj'⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d' S' M' e' hS' T' ρ' j' H'
  have hF : ∀ g, LinearMap.toMatrix b b' f * LinearMap.toMatrix b b (ρ g) =
      LinearMap.toMatrix b' b' (ρ' g) * LinearMap.toMatrix b b' f := fun g => by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext (hf g)
  obtain ⟨Y, hY⟩ := GlobalTheory.T.equivariant_latticeMatrix_over_breuilKisin l K bk d d' S S' _ _ U U' hU hU' _ hF
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_fCrystalHom_of_stratifiedPhiModuleHom l K bk d d' S S' M M' e e' hS hS' Y
    (GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant l K bk d d' S S' _ _ U U' hU hU' _ hF Y hY)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  refine ⟨u, fun x => ?_⟩
  refine semilinear_square_of_basis β (u.u (ainfObj K)) j j' (f.baseChange (WCb l)) (fun k => ?_) x
  refine square_column (M.tr bk.ι) (M'.tr bk.ι) (u.u bk.prism) (u.u (ainfObj K)) j j' (f.baseChange (WCb l))
    (u.u_tr bk.ι) (hβ k) (hu k) (hj k) hj' ?_
  exact sum_smul_column_eq b b' f U U' _ hY k

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApproxOfArtinTrivialStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_approx_of_artin_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ), art (Neutral.B1.localIdele E w x) = 1 →
    (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t) := by
  first | exact @GlobalTheory.ArtinApprox.exists_global_approx | exact GlobalTheory.ArtinApprox.exists_global_approx | (intros; apply GlobalTheory.ArtinApprox.exists_global_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeRepresentativesRightTranslateIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.UpInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levW_le_GfC (R : RealDat D A Ks) (i : Fin D.R.m) {k : GA D (Wc D i)} (hk : k ∈ levW R i) :
    k ∈ GfC (Wc D i) := hk.1

theorem mem_locK_iff (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC (Wc D i)) :
    (g : GA D (Wc D i)) ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} ↔
      g ∈ KR R i ∧ cf (Wc D i) v g = g := by
  simp only [Set.mem_setOf_eq, KR, Subgroup.mem_subgroupOf, cf_eq_self_iff]

theorem dcRep_exists (R : RealDat D A Ks) (i : Fin D.R.m) (hT : TransLaws R i)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i)) (hα : cf (Wc D i) v α = α) :
    ∃ C, DCRep (cf (Wc D i) v) (KR R i) α C := by
  classical
  obtain ⟨C, hsupp, hrep⟩ := hT.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα)
  refine ⟨C.subtype (· ∈ GfC (Wc D i)), fun δ hδ => ?_, fun x ⟨k₁, k₂, h1, h2, h3, h4, hx⟩ => ?_⟩
  · rw [Finset.mem_subtype] at hδ
    refine ⟨(cf_eq_self_iff _ v δ).2 (hsupp _ hδ), ?_⟩
    obtain ⟨-, k₁, hk₁, k₂, hk₂, he⟩ := hrep.1 _ hδ
    refine ⟨⟨k₁, levW_le_GfC R i hk₁.1⟩, ⟨k₂, levW_le_GfC R i hk₂.1⟩, ?_⟩
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, levW_le_GfC R i hk₁.1⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, levW_le_GfC R i hk₂.1⟩).1 hk₂
    exact ⟨a1, a2, b1, b2, Subtype.ext he⟩
  · have hk₁ := (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩
    have hk₂ := (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩
    have hx' : (x : GA D (Wc D i)) = (k₁ : GA D (Wc D i)) * α * k₂ := by rw [hx]; rfl
    obtain ⟨γ, ⟨hγC, hγK⟩, huniq⟩ := hrep.2 x ⟨_, hk₁, _, hk₂, hx'⟩
    have hγG : γ ∈ GfC (Wc D i) := (hrep.1 γ hγC).1
    have e : ((⟨γ, hγG⟩⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = γ⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm := (mem_locK_iff R i v (⟨γ, hγG⟩⁻¹ * x)).1 (by rw [e]; exact hγK)
    refine ⟨⟨γ, hγG⟩, ⟨Finset.mem_subtype.2 hγC, hm⟩, ?_⟩
    rintro δ ⟨hδC, hδK, hδc⟩
    have e' : ((δ⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm' := (mem_locK_iff R i v (δ⁻¹ * x)).2 ⟨hδK, hδc⟩
    rw [e'] at hm'
    exact Subtype.ext (huniq (δ : GA D (Wc D i)) ⟨Finset.mem_subtype.1 hδC, hm'⟩)

theorem isCosetRep_map (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i))
    (C : Finset (GfC (Wc D i))) (hC : DCRep (cf (Wc D i) v) (KR R i) α C) :
    (∀ γ ∈ C.map (Function.Embedding.subtype _), SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} α
        (C.map (Function.Embedding.subtype _)) := by
  classical
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_, fun x ⟨k₁, hk₁, k₂, hk₂, hx⟩ => ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    exact (cf_eq_self_iff _ v δ).1 (hC.1 δ hδ).1
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨-, k₁, k₂, h1, h2, h3, h4, he⟩ := hC.1 δ hδ
    refine ⟨δ.2, k₁, (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩, k₂, (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩, ?_⟩
    simp [he]
  · have g₁ := levW_le_GfC R i hk₁.1
    have g₂ := levW_le_GfC R i hk₂.1
    have hxG : x ∈ GfC (Wc D i) := by
      rw [hx]; exact (GfC (Wc D i)).mul_mem ((GfC (Wc D i)).mul_mem g₁ α.2) g₂
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, g₁⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, g₂⟩).1 hk₂
    have hx2 : (⟨x, hxG⟩ : GfC (Wc D i)) = ⟨k₁, g₁⟩ * α * ⟨k₂, g₂⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hx
    have hex := hC.2 ⟨x, hxG⟩ ⟨_, _, a1, a2, b1, b2, hx2⟩
    obtain ⟨δ, ⟨hδC, hδK, hδc⟩, huniq⟩ := hex
    have hm := (mem_locK_iff R i v (δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).2 ⟨hδK, hδc⟩
    have e : ((δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e] at hm
    refine ⟨(δ : GA D (Wc D i)), ⟨Finset.mem_map_of_mem _ hδC, hm⟩, ?_⟩
    rintro γ ⟨hγC, hγK⟩
    obtain ⟨δ', hδ', rfl⟩ := Finset.mem_map.1 hγC
    have e' : ((δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ' : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨c1, c2⟩ := (mem_locK_iff R i v (δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).1 (by rw [e']; exact hγK)
    exact congrArg Subtype.val (huniq δ' ⟨hδ', c1, c2⟩)

theorem heckeReps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m),
    TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)),
    (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) →
    (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧
    (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C →
      ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hT B hB
  refine ⟨fun v α hα => dcRep_exists R i hT v α hα, fun v α C hα hC γ => ?_⟩
  obtain ⟨hs, hr⟩ := isCosetRep_map R i v α C hC
  have hB1 : ∀ y, B 1 y = y := fun y => ext_inner_left ℂ fun x => by
    rw [← hB, OneMemClass.coe_one, hT.2.2.2.2.2]
  have key : ∀ (γ : GfC (Wc D i)) y y', (∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' =
      ∑ δ ∈ C.map (Function.Embedding.subtype _), trPair R i (γ * δ) x y) →
      B γ y' = (∑ δ ∈ C, B (γ * δ)) y := fun γ y y' h => ext_inner_left ℂ fun x => by
    rw [← hB, h γ γ.2 x, Finset.sum_map, ContinuousLinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hB]; rfl
  ext y
  obtain ⟨y', -, hy'⟩ := hT.2.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα) _ hs hr y
  have e1 := key 1 y y' hy'
  simp only [one_mul, hB1] at e1
  rw [ContinuousLinearMap.mul_apply, ← e1, key γ y y' hy']

end GlobalTheory.UpInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocksStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  first | exact @GlobalTheory.SmallerParahoric.exists_mem_smaller | exact GlobalTheory.SmallerParahoric.exists_mem_smaller | (intros; apply GlobalTheory.SmallerParahoric.exists_mem_smaller <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  first | exact @GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | exact GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | (intros; apply GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one <;> assumption)
end

