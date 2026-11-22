import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieComb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

section SqLevPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev

open GlobalTheory.TorsFac

theorem factor_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (N ℓ : ℕ) (hodd : Odd N) (hMN : l.M ∣ N) (hp : ℓ.Prime) :
    ∃ (k n' Bn j : ℕ) (β : 𝓞 E), ℓ ^ k ∣ l.M ∧ Nat.Coprime n' ℓ ∧
      (N : 𝓞 E) = β * ((ℓ ^ k : ℕ) : 𝓞 E) * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ ℓ ^ (2 * k) * Bn = ℓ ^ j ∧
      ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) →
        t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * ℓ ^ (2 * k)) = 1 := by
  have hN : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hM : l.M ≠ 0 := by
    intro h
    rw [h] at hMN
    exact hN (zero_dvd_iff.1 hMN)
  obtain ⟨e, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN ℓ hp.ne_one
  obtain ⟨k, m, hm', hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hp.ne_one
  have hcop : Nat.Coprime n' ℓ := ((hp.coprime_iff_not_dvd).2 hn').symm
  have hcm : Nat.Coprime m ℓ := ((hp.coprime_iff_not_dvd).2 hm').symm
  have hMN' : ℓ ^ k * m ∣ ℓ ^ e * n' := hNe ▸ hMe ▸ hMN
  have hke : k ≤ e := by
    have h1 : ℓ ^ k ∣ ℓ ^ e * n' := (Dvd.intro _ rfl).trans hMN'
    have h2 : ℓ ^ k ∣ ℓ ^ e := (Nat.Coprime.pow_left k hcop.symm).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  obtain ⟨kk, hkk⟩ : m ∣ n' := (hcm.pow_right e).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hMN')
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le hke
  refine ⟨k, n', ℓ ^ (2 * e'), 2 * (k + e'), (ℓ : 𝓞 E) ^ e', ⟨m, hMe⟩, hcop, ?_, ?_, by ring,
    fun T t ht => ⟨?_, ?_⟩⟩
  · rw [hNe]; push_cast; ring
  · rw [map_pow, map_natCast]; push_cast; ring
  · obtain ⟨k2, hk⟩ := hMN
    have := kill Xo t N ht (N : 𝓞 E) (by rw [hk, Nat.cast_mul]; exact l.Mb.mul_mem_right _ (M_mem l))
    rw [← act_nat, ← this]
    congr 2
    push_cast; ring
  · have := kill Xo t N ht ((l.M : 𝓞 E) * kk) (l.Mb.mul_mem_right _ (M_mem l))
    rw [act_pow, ← this]
    congr 2
    rw [hNe, hMe, hkk]; push_cast; ring

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem class_bound_of_trivAt_pow (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [htp b]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨k, n', Bn, j, β₀, hkM, h1, h2, h3, h4, h5⟩ := factor_pow Xo N ℓ hL.1 hL.2.1 hℓ
  have hA : ((ℓ ^ k : ℕ) : 𝓞 E) * H.bar ((ℓ ^ k : ℕ) : 𝓞 E) = ((ℓ ^ (2 * k) : ℕ) : 𝓞 E) := by
    rw [map_natCast]; push_cast; ring
  have key : ∃ u : ℕ, u ∣ l.M ∧ ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w (u : 𝓞 E) *
      (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) :=
    ⟨ℓ ^ k, hkM, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b)).1) hF htr n' (ℓ ^ (2 * k)) Bn j _ β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b)).2)⟩
  obtain ⟨u, ⟨m, hm⟩, h⟩ := key
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point

end GlobalTheory.CovInt.SqLev

end SqLevPoint

section SqLevShort
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in

theorem smul_nonneg_of_shortRule (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) (hM0 : d.l₂.M ≠ 0)
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la,
        0 ≤ v ((betaH (Dw := Dw) c Λ * ((GlobalTheory.CovInt.intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  have hZ : GlobalTheory.CovInt.intZ D Dw d.l₂ n w = Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) := by
    rw [GlobalTheory.CovInt.intZ, hQ, _root_.mul_assoc]
  rw [hZ]
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have key := fun q => class_bound_of_trivAt_pow d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (fun b => (htp q b).1) (hF q) htr
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ]
    exact GlobalTheory.CovInt.ram_sum_le_vV_discr D.host.E T' _ (fun p hp => Nat.prime_of_mem_primeFactors hp) (r * e) _
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.CovInt.SqLev

end SqLevShort

namespace GlobalTheory.CovInt.SqLev

theorem smul_intZ_sq_nonneg_of_sq_dvd : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ℓ ^ 2 ∣ d.l₂.M → Λ.TrivAt ℓ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem _ htr v hv
  have h := smul_nonneg_of_shortRule D H Dw l Xo c n d hlev hnab (fun k _ _ y => by rw [pow_one]; exact hroot k y)
    hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem htr v hv
  have hV := isVal_valSet (Xo := Xo) (c := c) (cls := algCls Xo c) la v hv
  have hns : ∀ m : ℕ, 0 ≤ v (m • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g)) := by
    intro m
    induction m with
    | zero => rw [zero_smul, hV.zero]; exact le_top
    | succ m ih => rw [succ_nsmul]; exact (le_min ih h).trans (hV.add _ _)
  have e1 : (betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g =
      (intZ D Dw d.l₂ n w) • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
    rw [← Nat.cast_smul_eq_nsmul c.F, smul_smul]
    congr 1
    push_cast; ring
  rw [e1]
  exact hns _

end GlobalTheory.CovInt.SqLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hv : v ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  GlobalTheory.T.frameStabiliser_mapsTo_completedLattice β Λ hβ x hx v hv

theorem sEquiv_of_mul_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))
    (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin r) (Fin r) E)
    (hs : GlobalTheory.SUVol.IsSA G s) (hs' : GlobalTheory.SUVol.IsSA G s') (hM : GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M)
    (he : s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s) (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv G L 1 s' s :=
  GlobalTheory.T.special_unitary_kottwitz_equivalence G L s s' M γ hs hs' hM he hγ

theorem isUA_of_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (k : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : GlobalTheory.UCls.IsUA c (-G) k) : GlobalTheory.UCls.IsUA c G k := by
  have e : ∀ x y, GlobalTheory.AdLat.hermA c (-G) x y = -GlobalTheory.AdLat.hermA c G x y := by
    intro x y
    simp only [GlobalTheory.AdLat.hermA, Matrix.neg_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]
  refine ⟨h.1, fun x y => ?_⟩
  have := h.2 x y
  rw [e, e] at this
  exact neg_injective this

theorem mulVec_mem_hat (D : D7) {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (k : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hk : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St β)
    (x : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (hx : x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    k.1 *ᵥ x ∈
      GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ x hx
  have h2 := mulVec_mem_hatL β Λ hβ _ hk _ h1
  have h3 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h2
  convert h3 using 1
  funext a
  simp only [Matrix.mulVec, dotProduct, Formalism.UG.bc, Formalism.IndefR.Lev.swapAE, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]
  simp

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem sEquiv_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} (h : n = r)
    (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (s s' : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E))
    (k : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin n) (Fin n) E)
    (hs : GlobalTheory.SUVol.IsSA (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) s)
    (hs' : GlobalTheory.SUVol.IsSA (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) s')
    (hkU : GlobalTheory.UCls.IsUA (IsCMField.complexConj E) (-Jᵀ) k)
    (hk1 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)),
      k *ᵥ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)))
    (hk2 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin n → E)), k *ᵥ y = x)
    (he : s'.submatrix (Fin.cast h) (Fin.cast h) * k =
      GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s.submatrix (Fin.cast h) (Fin.cast h))
    (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv (Matrix.transpose (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
      ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) 1 s' s := by
  subst h
  have eΛ : Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast rfl)) = Λ := by
    ext x; rfl
  have eJ : Matrix.transpose (J.submatrix (Fin.cast (rfl : n = n).symm) (Fin.cast (rfl : n = n).symm)) = Jᵀ := by
    ext a b; rfl
  have es : ∀ t : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E),
      t.submatrix (Fin.cast rfl) (Fin.cast rfl) = t := fun t => by ext a b; rfl
  rw [eΛ, eJ]
  rw [eJ] at hs hs'
  rw [es, es] at he
  refine sEquiv_of_mul_eq _ _ s s' k γ hs hs' ⟨isUA_of_neg _ _ _ hkU, fun x hx => ⟨k *ᵥ x - x,
    sub_mem (hk1 x hx) hx, by simp⟩, hk2⟩ he hγ

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem finHom_rat (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : Theta.GA D V) (γ : GL (Fin V.rank) D.host.E)
    (hg : Theta.matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    (Theta.finHom V g).1 = (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have : Theta.finHom V g = Formalism.UG.bc (Algebra.TensorProduct.map (sndA D.host.F)
      (AlgHom.id D.host.F D.host.E)).toRingHom (Theta.matHom V g) := rfl
  rw [this, hg]
  ext a b
  simp [Formalism.UG.bc, GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem det_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hx : x ∈ Formalism.L2.DIV.St β) : x.1.det ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨y, rfl⟩ := hx
  have e : (Formalism.L2.DIV.frGL β y).1.det = (Formalism.L2.DIV.intGL F E n y).1.det := by
    show (β * Formalism.L2.DIV.intGL F E n y * β⁻¹).1.det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      Units.inv_mul, Matrix.det_one, one_mul]
  rw [e]
  have e2 : (Formalism.L2.DIV.intGL F E n y).1 = (Formalism.L2.Herm.intAf F E).subtype.mapMatrix y.1 := rfl
  rw [e2, ← RingHom.map_det]
  exact (y.1.det).2

set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s → ∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i (s j'))⁻¹ * g * GlobalTheory.MassLink.lift D i (s j)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j') := by
  intro D Tu Cl t0 hCl i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  intro J s hS j j' g γ _ hgm hk
  obtain ⟨-, hl⟩ := GlobalTheory.MassLift.lift_spec D i (s j) (hS.1 j)
  obtain ⟨-, hl'⟩ := GlobalTheory.MassLift.lift_spec D i (s j') (hS.1 j')
  have hfg := finHom_rat D (Wc D i) g γ hgm
  set k := Theta.finHom (Wc D i) ((GlobalTheory.MassLink.lift D i (s j'))⁻¹ * g * GlobalTheory.MassLink.lift D i (s j)) with hkdef
  have hkeq : (Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i (s j'))).1 * k.1 =
      (Theta.finHom (Wc D i) g).1 * (Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i (s j))).1 := by
    rw [← Units.val_mul, ← Units.val_mul, hkdef, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hl, hl', hfg] at hkeq
  have hSt : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St (Cl.βW i) := Formalism.L2.DIV.parLev_St hk.1
  have hfr : Formalism.L2.DIV.IsFrame (Cl.βW i) (Cl.ΛW i) := by obtain ⟨c, h, -⟩ := hCl.βW i; exact h
  have hdet1 : ∀ t : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E),
      GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) t → (t.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i))).det = 1 := by
    intro t ht
    exact (Matrix.det_submatrix_equiv_self (finCongr (rank_Wc i)) t).trans ht.2
  have hdk : k.1.det = (1 : Af D.host.F) ⊗ₜ[D.host.F] γ.1.det := by
    have := congrArg Matrix.det hkeq
    rw [Matrix.det_mul, Matrix.det_mul, hdet1 _ (hS.1 j), hdet1 _ (hS.1 j'), one_mul, mul_one] at this
    rw [this]
    exact (RingHom.map_det (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom _).symm
  refine ⟨?_, fun hγ => ?_⟩
  · have hm := det_mem_intAf _ _ hSt
    have e : (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k).1.det = Formalism.L2.Col.iA D.host.F D.host.E
        γ.1.det := by
      show ((Formalism.IndefR.Lev.swapAE D).mapMatrix k.1).det = _
      rw [← RingHom.map_det, hdk]
      rfl
    rw [e] at hm
    obtain ⟨c, hc⟩ := GlobalTheory.RatInt.mem_range_of_iA_mem _ hm
    rw [← hc]
    exact RingOfIntegers.isIntegral_coe c
  · have hU : GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-((Wc D i).gram)ᵀ)
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) :=
      GlobalTheory.FinUA.isUA_finHom D (Wc D i) _
    have h1 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) *ᵥ x ∈
          GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) :=
      fun x hx => mulVec_mem_hat D (Cl.βW i) (Cl.ΛW i) hfr k hSt x hx
    have hSt' : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k⁻¹ ∈ Formalism.L2.DIV.St (Cl.βW i) := by
      rw [map_inv]; exact inv_mem hSt
    have h2 : ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
        ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Cl.ΛW i : Set (Fin (Wc D i).rank → D.host.E)),
          (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) *ᵥ y = x := by
      intro x hx
      refine ⟨(k⁻¹).1 *ᵥ x, mulVec_mem_hat D (Cl.βW i) (Cl.ΛW i) hfr k⁻¹ hSt' x hx, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have he : (s j').submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) *
        (k.1 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E) γ.1 * (s j).submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) :=
      hkeq
    have hE := sEquiv_cast (rank_Wc i) (Wc D i).gram (Cl.ΛW i) (s j) (s j') k.1 γ.1 (hS.1 j) (hS.1 j') hU h1 h2 he hγ
    exact (hS.2.1 j' j hE).symm

end GlobalTheory.MassLinkConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLiftStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_group_pullback_epsilon_lift : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)), IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' → ψ f k' + ψ k g = 0 := by
  first | exact @GlobalTheory.KSSym.ks_symm | exact GlobalTheory.KSSym.ks_symm | (intros; apply GlobalTheory.KSSym.ks_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLettersIntegralLieBasisEigenframeRelationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_letters_integralLieBasis_eigenframe_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : GlobalTheory.LamT.LocMod z T iK),
    (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) →
    ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, GlobalTheory.LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A →
    letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
    ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
      (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
      φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
      GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
      ∃ (nu mu : Fin z.Φ.T.g → TanM yT.x Xo.univ.t.G) (C : (Σ b : E →+* ℂ, Fin (Dw.mult b)) → Fin z.Φ.T.g → T.Fr),
        (∀ σ k, C σ k ∈ Set.range (algebraMap T.V T.Fr)) ∧
        (∀ σ, fullB yT σ = ∑ k, iK (z.U (z.e σ) k) • nu k) ∧
        (∀ k, mu k = ∑ l, iK (A k l) • nu l) ∧
        ∀ b i, ∑ j, g b i j • fullB yT ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k := by
  first | exact @GlobalTheory.LamT.TanRel.tangent_letter_model_relation | exact GlobalTheory.LamT.TanRel.tangent_letter_model_relation | (intros; apply GlobalTheory.LamT.TanRel.tangent_letter_model_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  first | exact @GlobalTheory.TransLift.lift_isTranslate | exact GlobalTheory.TransLift.lift_isTranslate | (intros; apply GlobalTheory.TransLift.lift_isTranslate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieCombStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  first | exact @GlobalTheory.isD_lieComb | exact GlobalTheory.isD_lieComb | (intros; apply GlobalTheory.isD_lieComb <;> assumption)
end

