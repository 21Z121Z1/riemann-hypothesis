import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0994
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0998
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTopOfOneMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjConjNeBot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • modul P c ≠ ⊥ := fun h => modul_ne_bot P c (by rw [← conj_conj_smul (modul P c), h, Ideal.smul_bot])

theorem conj_conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • D.host.conj • modul P c ≠ ⊥ := by
  rw [conj_conj_smul]
  exact modul_ne_bot P c

theorem kill (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {I : Ideal (𝓞 D.host.E)} {y u : WO S T}
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) (hu : u ∈ latO S T LS LT (fun _ => True))
    {b : 𝓞 D.host.E} (hb : b ∈ D.host.conj • I) : ψ (symplO S T (incA D (b : D.host.E) • u) y) = 1 := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_int]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu (hy _ (mem_conj_smul.1 hb))

theorem smul_finRat_mem (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P : Finset (Formalism.L2.DIV.Pl D.host.E))
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    ∀ m ∈ modul P c, incA D (m : D.host.E) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) := fun m hm => by
  rw [smul_finRat, finRat_mem_iff hψ hcc gS hLS hLT hS hT]
  exact smul_skew_mem (conj_conj_ne_bot P c) hz (by rwa [conj_conj_smul])

theorem kill_of_inId (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) {I : Ideal (𝓞 D.host.E)} {t y : WO S T}
    (ht : IsHalf (cA D e) t) (hI : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • I) (toEAf D (t i j)))
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) : ψ (symplO S T t y) = 1 := by
  obtain ⟨hinf, hint, -⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props _ _ (fun _ => 0) (GlobalTheory.RefDatumLev.isIdemSum_conjPl he.1)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he.1]
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (D.host.conj • I))
  have hfI : ∀ k, f k ∈ D.host.conj • I := fun k => hf ▸ Submodule.subset_span ⟨k, rfl⟩
  have hc : ∀ i j, ∃ c : Fin n → Formalism.L2.Theta.AE D, (∀ k, toEAf D (c k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      toEAf D (t i j) = ∑ k, toEAf D (incA D (f k : D.host.E)) * toEAf D (c k) := fun i j => by
    obtain ⟨h1, h2⟩ := hI i j
    have e1 : Formalism.L2.DIV.idS D.host.F (D.host.conj • I) =
        Ideal.span (Set.range fun k => Formalism.L2.DIV.oToS D.host.F D.host.E (f k)) := by
      rw [Formalism.L2.DIV.idS, ← hf]
      refine (Ideal.map_span _ _).trans ?_
      rw [← Set.range_comp]
      rfl
    rw [e1, Ideal.mem_span_range_iff_exists_fun] at h2
    obtain ⟨r, hr⟩ := h2
    choose c hc using fun k => toEAf_surj (D := D) (r k : EAf D)
    refine ⟨c, fun k => hc k ▸ (r k).2, ?_⟩
    have h3 := congrArg (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype hr
    rw [map_sum] at h3
    refine h3.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, hc, mul_comm]
    rfl
  choose c hc1 hc2 using hc
  let u : Fin n → WO S T := fun k => Matrix.of fun i j => cA D e * c i j k
  have hu1 : ∀ k, IsHalf (cA D e) (u k) := fun k i j => by
    change cA D e * (cA D e * c i j k) = cA D e * c i j k
    rw [← mul_assoc, hee]
  have hu2 : ∀ k, u k ∈ latO S T LS LT (fun _ => True) := fun k =>
    (half_mem_iff hcc hLS hLT hS hT he _ (hu1 k)).2 fun i j => by
      change toEAf D (cA D e * c i j k) ∈ _
      rw [RingHom.map_mul]
      exact mul_mem hint (hc1 i j k)
  have hent : ∀ i j, (∑ k, incA D (f k : D.host.E) • u k) i j = cA D e * ∑ k, incA D (f k : D.host.E) * c i j k :=
    fun i j => by
      rw [Matrix.sum_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have e2 : t = ∑ k, incA D (f k : D.host.E) • u k := half_ext hinf ht
    (fun i j => by rw [hent, ← mul_assoc, hee]) fun i j => by
      rw [hent, ← ht i j, RingHom.map_mul, RingHom.map_mul, hc2, map_sum]
      simp only [RingHom.map_mul]
  rw [e2]
  exact Finset.sum_induction _ (fun t => ψ (symplO S T t y) = 1)
    (fun a b ha hb => by rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, ha, hb, one_mul])
    (by rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]) fun k _ => kill hψ hS hT hy (hu2 k) (hfI k)

theorem inId_of_kill (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {t : WO S T}
    (ht : IsHalf (cA D e) t) (htΛ : t ∈ latO S T LS LT (fun _ => True))
    (hk : ∀ z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank),
      ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T z)) = 1) (i j) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (t i j)) := by
  have hN : 0 < Ideal.absNorm (D.host.conj • D.host.conj • modul P c) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (conj_conj_ne_bot P c))
  have h1 : ∀ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
      toEAf D (incA D (star s) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun s hs => by
    have hh : IsHalf (cA D e) (incA D (star s) • t) := fun i j => by
      change cA D e * (incA D (star s) * t i j) = incA D (star s) * t i j
      rw [mul_left_comm, ht]
    refine (half_mem_iff hcc hLS hLT hS hT he _ hh).1 ?_ i j
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1 _ (Matrix.ext fun i j => ?_)).2 fun u hu => ?_
    · have : infPart D (t i j) = 0 := congrFun (congrFun (GlobalTheory.VacUnique.latO_inf S T _ _ _ htΛ) i) j
      change infPart D (incA D (star s) * t i j) = 0
      rw [RingHom.map_mul, this, mul_zero]
    · obtain ⟨γ, hγ, v, hv, rfl⟩ := approx hψ hcc gS hLS hLT hS hT hN hu
      obtain ⟨b, -, hb⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (Ideal.absNorm_mem _)
      have e1 : incA D s • Ideal.absNorm (D.host.conj • D.host.conj • modul P c) • v = incA D (b : D.host.E) • v := by
        rw [hb, mul_comm, RingHom.map_mul, mul_smul]
        congr 1
        rw [← Nat.cast_smul_eq_nsmul (Formalism.L2.Theta.AE D)]
        congr 1
        exact (map_natCast ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm
      rw [GlobalTheory.PlaceModel.symplO_smul, GlobalTheory.DualPairCheck.cA_incA, star_star, smul_add, GlobalTheory.PlaceModel.symplO_add_right,
        AddChar.map_add_eq_mul, smul_finRat, hk _ (smul_mem_skew _ hs hγ), one_mul, e1]
      exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT htΛ (GlobalTheory.VacSign.smul_mem_latO b hv)
  have h2 : ∀ r ∈ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (incA D (star r) * t i j)) := fun r hr => by
    rw [← div_mul_cancel₀ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
      (FractionalIdeal.coeIdeal_ne_zero.2 (conj_conj_ne_bot P c))] at hr
    refine FractionalIdeal.mul_induction_on hr (fun s hs m hm => ?_) fun x y hx hy => ?_
    · obtain ⟨m, hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
      have e1 : star (s * algebraMap (𝓞 D.host.E) D.host.E m) = ((D.host.conj • m : 𝓞 D.host.E) : D.host.E) * star s := by
        rw [star_mul, star_eq (algebraMap (𝓞 D.host.E) D.host.E m)]
        rfl
      rw [e1, RingHom.map_mul (incA D), mul_assoc]
      exact inId_mul (mem_conj_smul.1 hm') (h1 s hs)
    · rw [star_add, RingHom.map_add, add_mul, RingHom.map_add]
      exact inId_add hx hy
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he.1 c)
  have h3 := h2 _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))
  have e2 : star (algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • a)) = (a : D.host.E) := by
    change star (D.host.conj (a : D.host.E)) = _
    rw [← star_eq, star_star]
  have e3 : t i j = incA D (b : D.host.E) * t i j + incA D (a : D.host.E) * t i j := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← add_mul, ← RingHom.map_add, this, RingHom.map_one, one_mul]
  rw [e2] at h3
  rw [e3, RingHom.map_add]
  exact inId_add (inId_mul hb ((half_mem_iff hcc hLS hLT hS hT he _ ht).1 htΛ i j)) h3

theorem heisO_eq_half (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {vac : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    heisO ψ S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) vac = heisO ψ S T (GlobalTheory.VacUnique.finRat S T (2 • z)) vac := by
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hy := smul_finRat_mem hψ hcc gS hLS hLT hS hT P c (nsmul_mem hz 2)
  have hl : (1 - e) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    GlobalTheory.AdTh.MovedSum.one_sub_smul_mem_latO_pow S T _ _ e P he _ fun s hs => ⟨∑ w ∈ P, c w,
      smul_finRat_mem hψ hcc gS hLS hLT hS hT P c hz _ (by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Ideal.prod_mem_prod fun w hw => Ideal.pow_mem_pow (hs w hw) _)⟩
  have e0 : cA D e • (1 - e) • GlobalTheory.VacUnique.finRat S T z = cA D e • GlobalTheory.VacUnique.finRat S T z := by
    rw [smul_smul, mul_sub, mul_comm (cA D e) e, he.2, sub_zero, mul_one]
  have hl' : cA D e • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    e0 ▸ GlobalTheory.PlaceModelSum.idem_smul_latO hee hl
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he c)
  have hA : ∀ w ∈ AddSubgroup.closure {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E |
      ∃ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
        (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank), w = s • γ},
      ψ (symplO S T (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T w) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨s, hs, γ, hγ, rfl⟩ := hw
      obtain ⟨b', hb', e1⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (m := a) (by rwa [conj_conj_smul])
      rw [smul_comm, smul_finRat, smul_smul, ← e1, ← smul_finRat, smul_comm]
      exact kill hψ hS hT hy (GlobalTheory.PlaceModelSum.idem_smul_latO hee ((finRat_mem_iff hψ hcc gS hLS hLT hS hT _).2 hγ)) hb'
    | zero => rw [map_zero, smul_zero, smul_zero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [map_add, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      have h := AddChar.map_zero_eq_one ψ
      rw [← GlobalTheory.PlaceModel.symplO_zero_left S T (GlobalTheory.VacUnique.finRat S T (2 • z)),
        ← add_neg_cancel (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T x), GlobalTheory.PlaceModel.symplO_add_left,
        AddChar.map_add_eq_mul, hx, one_mul] at h
      rwa [map_neg, smul_neg, smul_neg]
  have hB : ψ (symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← one_smul (Formalism.L2.Theta.AE D) (cA D e • GlobalTheory.VacUnique.finRat S T z), ← RingHom.map_one (incA D), ← this,
      RingHom.map_add, add_smul, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, kill hψ hS hT hy hl' hb,
      hA z (skew_mem_closure _ hz), one_mul]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  have hC : symplOH S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) =
      -symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z)) := by
    rw [symplOH, two_nsmul ((1 - e) • GlobalTheory.VacUnique.finRat S T z), GlobalTheory.PlaceModel.symplO_add_right,
      GlobalTheory.PlaceModel.symplO_smul, e0, ← GlobalTheory.PlaceModel.symplO_skew, ← two_mul, ← mul_assoc, h2, one_mul]
  have h := GlobalTheory.LatVac.heisO_heisO ψ (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) vac
  rw [hvac.1 _ hl, hC, AddChar.map_neg_eq_inv, hB, inv_one, one_smul] at h
  rw [h, map_nsmul, smul_comm 2 (1 - e), ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.SkewLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKContSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_big (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_small (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem measure_fundamental_domain_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) (μ : @Measure H (borel H))
    (hμ : @Measure.IsHaarMeasure H _ _ (borel H) μ) (D : Set H)
    (hD : letI := borel H; IsFundamentalDomain
      ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H) D μ) :
    μ D < ⊤ := by
  subst hH
  letI : MeasurableSpace (HR (AF F) σ J) := borel _
  haveI : BorelSpace (HR (AF F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, -, hcov, -, hvol, -⟩ := GlobalTheory.SiegelSet.exists_cover hS hσ hJ
  set Γ := (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf (HR (AF F) σ J)
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  haveI : Countable Γ := by
    have : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
      (MonoidHom.rangeRestrict_surjective _).countable
    exact Function.Injective.countable (f := fun γ : Γ =>
      (⟨γ.1.1, γ.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
      fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  haveI : MeasurableConstSMul Γ (HR (AF F) σ J) := ⟨fun γ => (continuous_mul_left γ.1).measurable⟩
  haveI : SMulInvariantMeasure Γ (HR (AF F) σ J) μ := ⟨fun γ s _ => measure_preimage_mul μ γ.1 s⟩
  refine lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun g => ?_)) (hvol μ hμ)
  obtain ⟨γ, ⟨δ, -, hδ⟩, s, hs, e⟩ := hcov g
  let γ' : Γ := ⟨γ, δ, hδ⟩
  refine ⟨γ'⁻¹, ?_⟩
  have : γ'⁻¹ • g = s := inv_smul_eq_iff.2 e
  rw [this]; exact hs

theorem measure_dom_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : B.IsGood σ) {n d r s : ℕ} {Y : Spc F E n} {W : Spc F E d}
    (hY : Y.IsHerm σ B r s) {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) : M.μ M.dom < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (hY.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hJ : IsHermND σ ((1 : E) • Y.J.map σ) := by
    rw [one_smul]
    refine ⟨fun i j => congrArg σ (hY.herm i j), ?_⟩
    have e : (Y.J.map σ).det = σ Y.J.det := ((σ : E →+* E).map_det _).symm
    rw [e]
    exact (map_ne_zero σ).2 hd
  exact measure_fundamental_domain_lt_top hS hB.cm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ one_ne_zero) M.μ hM.haar M.dom hM.dom

theorem contSmall : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT Φ' hΦ'
  have hPair := isPair_small hT
  have hSo : Φ' ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ').2
  have hS : Φ' ∈ schA F _ := so_le_schA hT.geo.hM' _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ' hS
  refine ⟨?_, fun γ hγ h => ?_⟩
  · obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ' hSo 0
    haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
    have hv := measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
    have hht : Continuous (fun h : UA σ G.W.J => (ht h : ℝ)) :=
      NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : SecondCountableTopology (AE F E) := by
      obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
      exact e.secondCountableTopology
    haveI hMat : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin (a + a') → Fin (a + a') → AE F E))
    haveI : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))).symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin (a + a')) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    haveI : SecondCountableTopology (UA σ G.W.J) :=
      (Topology.IsEmbedding.subtypeVal (p := fun x : GL (Fin (a + a')) (AE F E) => x ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J))).secondCountableTopology
    haveI : FirstCountableTopology (UA σ G.W.J) :=
      TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    rw [continuous_iff_continuousAt]
    intro h₀
    have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 :=
      hht.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    unfold Model.I
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun g => ?_
      have h1 := hC g h
      rw [pow_zero, mul_one] at h1
      calc ‖theta om' Φ' g h‖ ≤ C * (ht h : ℝ) ^ k := h1
        _ ≤ max C 0 * (ht h : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh.le _) (le_max_right _ _)
    · exact integrableOn_const hv.ne
    · exact Eventually.of_forall fun g =>
        (hB.1.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e := hB.2.1 1 (one_mem _) γ hγ g h
    rw [one_mul] at e
    exact e

end GlobalTheory.ThKContSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GlobalTheory.Mix

theorem continuousOn_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  intro k _ X p σ D L c y₀ hy₀
  let i : ∀ a, (L a).B.ι := fun a => pick (L a).φ.isLB y₀
  let S : Set (CxPts p σ) := c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))
  have hSo : IsOpen S := c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)
  have hy₀S : y₀ ∈ S := ⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩
  have hH : ∀ (a : Fin D) (j l : Fin D),
      ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S := by
    intro a j l
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      isOpen_over c.e (isOpen_ptsIn _)
    have hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)
    have hw := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l
    exact hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy =>
      ⟨c.e.map_source hy.1, by
        simpa only [mem_preimage, c.e.left_inv hy.1] using mem_iInter.1 hy.2 a⟩
  let F : CxPts p σ → ℝ := fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D),
    (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re
  have hF : ContinuousOn F S := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_finsetSum _ fun τ _ => ?_))
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l
  have he : ∀ y ∈ S, dens L c y = F y := by
    intro y hy
    have hm : ∀ τ : Equiv.Perm (Fin D),
        (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) =
          Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l := fun τ => by
      ext j l
      simp only [Matrix.of_apply]
      rw [c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]
    simp only [dens, F, hm]
  refine ContinuousAt.continuousWithinAt ?_
  refine (hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_
  filter_upwards [hSo.mem_nhds hy₀S] with y hy
  exact (he y hy).symm

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degData_from_lowerBase_after_monomial_extension : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  first | exact @GlobalTheory.PullFrom.degFrom_of_periodRel | exact GlobalTheory.PullFrom.degFrom_of_periodRel | (intros; apply GlobalTheory.PullFrom.degFrom_of_periodRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), m.Coprime p → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.kernel_descent | exact GlobalTheory.UPel.HT.Hecke.kernel_descent | (intros; apply GlobalTheory.UPel.HT.Hecke.kernel_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (exact GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (intros; apply GlobalTheory.det_aeval_eq_prod_aroots_charpoly  <;> assumption)
end

