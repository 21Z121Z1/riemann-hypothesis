import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0888
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeMonicPolyLabelsSemisimpleParameterStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefree_monic_poly_labels_semisimple_parameter : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]), f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f → ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  first | exact @GlobalTheory.ParamExists.param_exists | exact GlobalTheory.ParamExists.param_exists | (intros; apply GlobalTheory.ParamExists.param_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebraStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_split | exact GlobalTheory.QSA.strongApprox_split | (intros; apply GlobalTheory.QSA.strongApprox_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

theorem tmul_mem_intAE (a : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), a, rfl⟩

theorem mul_mem_idealHat {I : Ideal (𝓞 D.host.E)} {y z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ idealHat D I) (hy : y ∈ intAE D) : z * y ∈ idealHat D I := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨b, hb, t * y, mul_mem_intAE ht hy, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

theorem mem_idealHat_of_idS {I : Ideal (𝓞 D.host.E)} {s : LatticeBasisLifts.OAf D} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, swapAE D z = (s : EAf D) → z ∈ idealHat D I := by
  have hb : Function.Surjective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective
  induction hs using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    intro z hz
    refine AddSubgroup.subset_closure ⟨b, hb, 1, tmul_mem_intAE 1, ?_⟩
    rw [mul_one]
    exact swapAE_injective hz
  | zero =>
    intro z hz
    rw [show z = 0 from swapAE_injective (hz.trans (swapAE D).map_zero.symm)]
    exact zero_mem _
  | add a b _ _ h1 h2 =>
    intro z hz
    obtain ⟨p, hp⟩ := hb (a : EAf D)
    obtain ⟨q, hq⟩ := hb (b : EAf D)
    rw [show z = p + q from swapAE_injective (by rw [RingHom.map_add, hp, hq]; exact hz)]
    exact add_mem (h1 p hp) (h2 q hq)
  | smul a b _ h2 =>
    intro z hz
    obtain ⟨p, hp⟩ := hb (a : EAf D)
    obtain ⟨q, hq⟩ := hb (b : EAf D)
    rw [show z = q * p from swapAE_injective (by rw [RingHom.map_mul, hp, hq, mul_comm]; exact hz)]
    exact mul_mem_idealHat (h2 q hq) ((mem_intAE_iff p).2 (hp ▸ a.2))

theorem bar_coe (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) :
    D.sp.cm.sig (a : D.host.E) = (H.bar a : D.host.E) := (H.bar_eq a).symm

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hz : z ∈ intAE D) : sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, H.bar x, congrArg (a ⊗ₜ[D.host.F] ·) (bar_coe H x)⟩
  exact this hz

theorem cA_mem_idealHat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {I J : Ideal (𝓞 D.host.E)}
    (h : ∀ b ∈ I, H.bar b ∈ J) {z : AE D} (hz : finPart D z ∈ idealHat D I) :
    finPart D (cA D z) ∈ idealHat D J := by
  rw [(parts_cA z).2]
  have : idealHat D I ≤ (idealHat D J).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨H.bar b, h b hb, _, sigR_mem_intAE H hy, ?_⟩
    refine ((sigR (Af D.host.F) D.sp.cm.sig).map_mul _ _).trans (congrArg (· * _) ?_)
    exact congrArg ((1 : Af D.host.F) ⊗ₜ[D.host.F] ·) (bar_coe H b)
  exact this hz

theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem conj_quot_congr {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (O A B : AddSubgroup S)
    (hA : ∀ z ∈ A, ∀ y ∈ O, z * y ∈ A) (hO : ∀ z, f z ∈ O → f (c z) ∈ O)
    (hAB : ∀ z, f z ∈ A → f (c z) ∈ B) (hBA : ∀ z, f z ∈ B → f (c z) ∈ A) (x X Xi : R) (hX : X * Xi = 1)
    (a a' : S) (ha' : a' ∈ O) (h1 : f x - a ∈ A) (h2 : f X - a ∈ A) (h3 : f X - 1 ∈ B) (h4 : f Xi ∈ O)
    (h5 : f (c x) - a' ∈ A) : f (c (x * Xi)) - a' ∈ A ∧ f (c (x * Xi)) - 1 ∈ B := by
  have e1 : f X * f Xi = 1 := by rw [← map_mul, hX, map_one]
  have e2 : f (c X) * f (c Xi) = 1 := by rw [← map_mul, ← map_mul, hX, map_one, map_one]
  constructor
  · have h6 := hBA (X - 1) (by rwa [map_sub, map_one])
    rw [map_sub, map_one, map_sub, map_one] at h6
    have h8 := hA _ (sub_mem h5 (hA _ h6 _ ha')) _ (hO _ h4)
    convert h8 using 1
    rw [map_mul, map_mul]
    linear_combination a' * e2
  · have h6 := hAB (x * Xi - 1) (by
      convert hA _ (sub_mem h1 h2) _ h4 using 1
      rw [map_sub, map_mul, map_one]
      linear_combination e1)
    rwa [map_sub, map_one, map_sub, map_one] at h6

theorem finUnit_of_unit {x : (AE D)ˣ} {u : (LatticeBasisLifts.OAf D)ˣ} (hx : infPart D (x : AE D) = 1)
    (hu : ((u : LatticeBasisLifts.OAf D) : EAf D) = swapAE D (finPart D (x : AE D))) : FinUnit x := by
  refine ⟨hx, (mem_intAE_iff _).2 (hu ▸ u.1.2), (mem_intAE_iff _).2 ?_⟩
  have e1 : swapAE D (finPart D (x : AE D)) * swapAE D (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]
  have e2 : (((u⁻¹ : (LatticeBasisLifts.OAf D)ˣ) : LatticeBasisLifts.OAf D) : EAf D) * ((u : LatticeBasisLifts.OAf D) : EAf D) = 1 :=
    congrArg Subtype.val u.inv_mul
  rw [hu] at e2
  rw [← left_inv_eq_right_inv e2 e1]
  exact Subtype.property _

theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])

theorem exists_congr {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (s : LatticeBasisLifts.OAf D)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hs : (s : EAf D) = swapAE D z) :
    ∃ a : 𝓞 D.host.E, resI D.host.F I hI s = Ideal.Quotient.mk I a ∧
      z - (1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E) ∈ idealHat D I := by
  obtain ⟨a, ha⟩ := exists_sub_mem I hI s
  refine ⟨a, (resI_eq_mk_iff I hI s a).2 ha, mem_idealHat_of_idS ha _ ?_⟩
  rw [RingHom.map_sub, ← hs]
  rfl

theorem chiProd_resI {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) {Pg : Finset (Formalism.L2.DIV.Pl E)} (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal)
    {K : Type} [Field K] (σ : K →+* ℂ) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ)
    (u ub : (Formalism.L2.Herm.intAf F E)ˣ) :
    ∏ w : ↥Pg, (σ ((χ w (Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom u) : Kˣ) : K))⁻¹ *
        σ ((χ w (Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom ub) : Kˣ) : K) =
      (σ ((chiProd hle χ (Units.map (resI F I hI).toMonoidHom u) : Kˣ) : K))⁻¹ *
        σ ((chiProd hle χ (Units.map (resI F I hI).toMonoidHom ub) : Kˣ) : K) := by
  have h : ∀ (v : (Formalism.L2.Herm.intAf F E)ˣ) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom
      (Units.map (resI F I hI).toMonoidHom v) = Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom v :=
    fun v w => Units.ext (factor_resI_eq_resS hI w.1 (hle w) v.1)
  simp only [chiProd_apply, h, Units.coe_prod, map_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem circle_step {G : Type} [CommGroup G] (μ : G →* Circle) (x X Y : G) (s t : ℂ) (h1 : s * (μ X : ℂ) = 1)
    (h2 : t * (μ Y : ℂ) = 1) (h3 : μ (x * X⁻¹ * Y) = 1) : (μ x : ℂ) = s⁻¹ * t := by
  have h4 : μ x * μ Y = μ X := by
    rw [← map_mul, ← one_mul (μ X), ← h3, ← map_mul, mul_right_comm x, inv_mul_cancel_right]
  have h5 : (μ x : ℂ) * μ Y = μ X := by rw [← Circle.coe_mul, h4]
  rw [← eq_inv_of_mul_eq_one_right h1]
  linear_combination t * h5 - (μ x : ℂ) * h2

set_option maxHeartbeats 800000 in

theorem isInvTame_of_half : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), (∀ x : (AE D)ˣ, cA D (x : AE D) = (x : AE D) → μ x = 1) → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) → LatticeBasisLifts.IsInvTame σ Pg μ χ := by
  intro D H l Pg hle K _ σ μ χ hfix hT x u ub hx hu hub
  have hM : l.Mb * l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥ := by
    rw [l.prod, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := l.three_le
    omega
  have hI : l.Mb ≠ ⊥ := fun h => hM (by rw [h, Ideal.bot_mul])
  have hJ : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥ := fun h => hM (by rw [h, Ideal.mul_bot])
  have hIJ : ∀ b ∈ l.Mb, H.bar b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    fun b hb => Ideal.mem_map_of_mem _ hb
  have hJI : ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), H.bar b ∈ l.Mb := fun b hb => by
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hb
    exact (bar_bar H c).symm ▸ hc
  obtain ⟨a, ha, ha2⟩ := exists_congr hI u.1 hu
  obtain ⟨b, hb, hb2⟩ := exists_congr hI ub.1 hub
  obtain ⟨X, hX, hX1, hX2⟩ := GlobalTheory.UnitResidue.exists_finUnit_congMod D _ _ hI hJ l.coprime a
    (ha ▸ (Units.map (resI D.host.F l.Mb hI).toMonoidHom u).isUnit)
  have hxu := finUnit_of_unit hx hu
  obtain ⟨hY1, hY2⟩ := conj_quot_congr (finPart D) (cA D) (intAE D) (idealHat D l.Mb) (idealHat D _)
    (fun z hz y hy => mul_mem_idealHat hz hy) (fun z hz => finPart_cA_mem hz)
    (fun z hz => cA_mem_idealHat H hIJ hz) (fun z hz => cA_mem_idealHat H hJI hz) x X (X⁻¹ : (AE D)ˣ) X.mul_inv _ _
    (tmul_mem_intAE b) ha2 hX1 hX2 hX.2.2 hb2
  have h1 := hT X hX a (Units.map (resI D.host.F l.Mb hI).toMonoidHom u) ha hX1 hX2
  have h2 := hT (Units.map (cA D).toMonoidHom (x * X⁻¹)) (FinUnit_conj (FinUnit_mul hxu (FinUnit_inv hX))) b
    (Units.map (resI D.host.F l.Mb hI).toMonoidHom ub) hb hY1 hY2
  have h3 := hfix (x * X⁻¹ * Units.map (cA D).toMonoidHom (x * X⁻¹)) (by
    show cA D (((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)) =
      ((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)
    rw [RingHom.map_mul, cA_cA, mul_comm])
  exact (circle_step μ x X _ _ _ h1 h2 h3).trans (chiProd_resI hI hle σ χ u ub).symm

end GlobalTheory.GeoActCompare.TameConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomRow

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem beta_eq_pow (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ^ 12 = latDisc Λ) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
  rw [beta, div_pow, ← pow_mul, mul_comm _ 12, pow_mul, hΩ]

theorem classTerm_rep [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    (hc : c ≠ ⊥) {χ : HChar E} (hinf : HasInf χ φ (fun i => (κ i : ℤ) + s)) (htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1)
    {l : ℕ} (hl : l.Prime) (hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S)
    (y : (Af E)ˣ) (S : ℂ → ℂ) (hS : IsLatSum φ (2 * s) κ (lattice c y) S) :
    ∃ y' : (Af E)ˣ, OneOver l y' ∧ ∃ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' ∧ ∃ u : ℂ, IntAt l u ∧
      ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = u * S' 0 := by
  obtain ⟨y', hy', hone⟩ := GlobalTheory.CMVal.TrivAbove.exists_rep_trivial_above E c l hc hl (QuotientGroup.mk y)
  obtain ⟨S', hS'⟩ := hex y'
  refine ⟨y', hone, S', hS', ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹, ?_, ?_⟩
  · have hu := GlobalTheory.CMVal.value_unitAt E I φ hφ s κ c χ l hc hl hinf htriv y' fun w hw => by
      rw [hone w hw, map_one]
    exact (GlobalTheory.CMVal.LUnit.unitAt_inv hu).2.1
  · exact GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ c χ hinf htriv y y' S S' hy'.symm hS hS'

theorem toricDenominator (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hR : LatIntRam) (hU : LatIntUnr) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  have hzc : IsClassZetaVals (2 * s) z := hz
  refine ⟨z, hzc, fun κ 𝔣 Λ χ hb hΛ hχ => ?_⟩
  have hUr : UnramFin E := hd.2.2.1
  have hφ : IsCMType φ := hd.2.2.2.2.2.2.1
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  intro l hl Q hQ hQl
  set c := condQ 𝔣 Q with hcdef
  have hc : c ≠ ⊥ := mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  have h0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hUr hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1 := fun u hu => h0 u (hatOUnits_mono hle hu)
  have hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := fun y =>
    GlobalTheory.CMVal.LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 c χ hUr hs hb
      (dvd_mul_right _ _) hc hχ.1 hχ.2.2.1 htriv y
  set x : ℂ → ℂ := fun T => (C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ with hxdef
  have hx : ∀ T, beta E d s κ Λ T = x T ^ 12 := fun T => beta_eq_pow d s κ Λ hΩ T
  have hxmul : ∀ u T, x (u * T) = u * x T := fun u T => by simp only [hxdef]; ring

  have hlat : ∀ y' : (Af E)ˣ, OneOver l y' → ∀ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (x (S' 0) ^ 12) := fun y' hy' S' hS' => by
    rw [← hx]
    by_cases h : c_vp 𝔣 l = 0
    · exact hU E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'
    · exact hR E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'

  have hterm : ∀ χ' : HChar E, HasInf χ' φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ' u = 1) →
      ∀ (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice c y) S →
      ∃ u w : ℂ, IntAt l u ∧ ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (w ^ 12) ∧
        x (((finPart χ' y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0) = u * w := by
    intro χ' hinf' htriv' y S hS
    obtain ⟨y', hy', S', hS', u, hu, e⟩ := classTerm_rep hφ hc hinf' htriv' hl hex y S hS
    exact ⟨u, x (S' 0), hu, hlat y' hy' S' hS', by rw [e, hxmul]⟩
  refine ⟨fun y T ⟨S, hS, hT⟩ => ?_, fun ψ T hψ ⟨hfin, S, hS, hT⟩ => ?_⟩
  · obtain ⟨u, w, hu, hw, e⟩ := hterm χ hχ.2.2.1 htriv y S hS
    have := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) Unit (fun _ => u) (fun _ => w) (fun _ => hu) (fun _ => hw)
    rw [hx, hT, e]
    simpa using this
  · have hinf' : HasInf (χ * ψ) φ (fun i => (κ i : ℤ) + s) := hχ.2.2.1.mul_triv hψ.1
    have htriv' : ∀ u ∈ hatOUnits c, finPart (χ * ψ) u = 1 := fun u hu => by
      show finPart χ u * finPart ψ u = 1
      rw [htriv u hu, hψ.2 u hu, one_mul]
    have := Fintype.ofFinite (PicO c)
    choose u w hu hw e using fun q : PicO c => hterm (χ * ψ) hinf' htriv' q.out (S q) (hS q)
    have key := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) (PicO c) u w hu hw
    rw [hx, hT, finsum_eq_sum_of_fintype]
    have : x (∑ q, ((finPart (χ * ψ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) = ∑ q, u q * w q := by
      rw [← Finset.sum_congr rfl fun q _ => e q]
      simp only [hxdef, Finset.mul_sum, Finset.sum_div]
    rw [this]
    exact key

end GlobalTheory.ToricDenomRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharactersStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_part_fibre_lie_algebra_characters : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  first | exact @GlobalTheory.torus_part_lie | exact GlobalTheory.torus_part_lie | (intros; apply GlobalTheory.torus_part_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraic
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.ToricCoordAlg

theorem isAlgebraic_coordIn : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ)
    (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  intro hA K _ _ d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV
  classical
  obtain ⟨hQ, hχ, hfin, S, hS, rfl⟩ := hV
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, GlobalTheory.TwistedTransportProof.coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) =
      ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [GlobalTheory.TwistedTransportProof.coordIn_eq d s κ Ω₀ (S q 0)]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h3 : IsAlgebraic ℚ ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ)) :=
    (GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hχ.2.2.1 htriv q.out).mul
      (GlobalTheory.TwistedTransportProof.isAlgebraic_modF_pow q.out s)
  refine mul_mem (inv_mem ?_) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.ToricCoordAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport
section
open GlobalTheory.LKCount

namespace GlobalTheory

theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' A B q1, ← DoubleCoset.out_eq' A B q2]
    obtain ⟨g, hg, k, hk, he⟩ := (DoubleCoset.eq Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
end

