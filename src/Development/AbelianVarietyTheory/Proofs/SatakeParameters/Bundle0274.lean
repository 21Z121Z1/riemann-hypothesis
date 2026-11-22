import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryOneFiniteAdelicOfDetNormOne
section
noncomputable section
namespace GlobalTheory.TwU
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneByOne
variable {R : Type} [CommRing R]

def oneByOne (x : Rˣ) : GL (Fin 1) R where
  val := Matrix.of fun _ _ => (x : R)
  inv := Matrix.of fun _ _ => ((x⁻¹ : Rˣ) : R)
  val_inv := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  inv_val := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]

end OneByOne

variable {D : D7}

theorem det_mem_normOne_of_mem_unitaryPoints {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} (hJ : IsUnit J.det)
    {g : GL (Fin n) (AfE D.host.F D.host.E)} (hg : g ∈ UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det g ∈ U1 (sigD D) := by
  set σR := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have h0 : Formalism.UG.cT σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) * J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) = J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hg
  have h1 := congrArg Matrix.det h0
  simp only [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have e1 : ((g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).map σR).det = σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det := by
    rw [RingHom.map_det]; rfl
  have e2 : (J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).det = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
    rw [RingHom.map_det]; rfl
  rw [e1, e2] at h1
  have hu : IsUnit (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det) := hJ.map _
  have h2 : σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det = 1 := by
    have : (σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det) *
        Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det = 1 * Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
      linear_combination h1
    exact hu.mul_right_cancel this
  show _ = _
  apply Units.ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, conjId, Units.coe_map, Units.val_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [mul_comm]
  exact h2

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}

open Classical in

def muTOf (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (mt : ℕ → D.Dt →* ℂˣ) (j : ℕ) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then ((mt j (dtU h.choose) : ℂˣ) : ℂ) else 1

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedResiduesInFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

namespace GlobalTheory.CRTFrame

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) (M : 𝓞 E) (hM : M ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P ((algebraMap (𝓞 E) E M)⁻¹ * algebraMap (𝓞 E) E z) := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {M} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hM
  have hex : ∃ m : ℕ, ¬ I ≤ P.asIdeal ^ m := by
    by_contra h
    push Not at h
    apply hI
    have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
    have := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal hP
    rw [eq_bot_iff, ← this]
    exact le_iInf h
  set m0 := Nat.find hex with hm0
  have hm0pos : m0 ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm0, h0, pow_zero] at this
    exact this (by rw [Ideal.one_eq_top]; exact le_top)
  refine ⟨m0 - 1, ?_⟩
  have hle : I ≤ P.asIdeal ^ (m0 - 1) := by
    have := Nat.find_min hex (show m0 - 1 < m0 by omega)
    push Not at this
    exact this
  have hnle : ¬ I ≤ P.asIdeal ^ (m0 - 1 + 1) := by
    rw [show m0 - 1 + 1 = m0 by omega]; exact Nat.find_spec hex
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hle
  have hQP : ¬ Q ≤ P.asIdeal := by
    intro h
    apply hnle
    rw [hQ, pow_succ]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.mp hQP
  intro z hz
  have hmem : z * s ∈ I := by
    rw [hQ]; exact Ideal.mul_mem_mul hz hsQ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hM' : algebraMap (𝓞 E) E M ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hM
  refine ⟨a, s, hsP, ?_⟩
  have h2 : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E M = algebraMap (𝓞 E) E z * algebraMap (𝓞 E) E s := by
    rw [← map_mul, ← map_mul, ha]
  field_simp
  linear_combination -h2

theorem approx_frames (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ) :
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  classical
  set w : SB → Sp E n := fun P => f P (y0 P) with hwdef
  set c : SB → Fin n → Fin n → E := fun P j l => (f P).symm (Pi.single j 1) l with hcdef
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    ((Finset.univ.image (fun x : SB × Fin n × Fin n => c x.1 x.2.1 x.2.2)) ∪
      (Finset.univ.image (fun x : SB × Fin n => w x.1 x.2)))
  set D : 𝓞 E := (b : 𝓞 E) with hDdef
  have hD : D ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hc : ∀ P j l, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * c P j l := by
    intro P j l
    obtain ⟨r, hr⟩ := hb (c P j l) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(P, j, l), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  have hw : ∀ P j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * w P j := by
    intro P j
    obtain ⟨r, hr⟩ := hb (w P j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(P, j), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose cr hcr using hc
  choose wr hwr using hw
  have hN : ∀ P : SB, ((qOf P.1 : ℕ) : 𝓞 E) ≠ 0 := by
    intro P
    rw [Ne, Nat.cast_eq_zero]
    show Ideal.absNorm P.1.asIdeal ≠ 0
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  set M : SB → 𝓞 E := fun P => ((qOf P.1 : ℕ) : 𝓞 E) ^ (e P) * D * D with hMdef
  have hM : ∀ P, M P ≠ 0 := fun P => mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hN P)) hD) hD
  choose k hk using fun P : SB => exists_pow_intAt_div P.1 (M P) (hM P)
  set kk : HeightOneSpectrum (𝓞 E) → ℕ := fun P => if h : P ∈ SB then k ⟨P, h⟩ else 0 with hkkdef
  have crt : ∀ j : Fin n, ∃ z : 𝓞 E, ∀ (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ SB),
      z - wr ⟨P, hP⟩ j ∈ P.asIdeal ^ kk P := fun j =>
    IsDedekindDomain.exists_forall_sub_mem_ideal (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) kk
      (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun P => wr P j)
  choose z hz using crt
  have hD' : algebraMap (𝓞 E) E D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hD
  refine ⟨fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j), ?_⟩
  intro P l
  have hexp : ∀ v : Sp E n, (f P).symm v l = ∑ j, v j * c P j l := by
    intro v
    have hv : v = ∑ j, v j • (Pi.single j 1 : Sp E n) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, Finset.sum_apply, c]
  have hmem : (∑ j, (z j - wr P j) * cr P j l) ∈ P.1.asIdeal ^ k P := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    have := hz j P.1 P.2
    simpa [kk, P.2] using this
  have key := hk P _ hmem
  convert key using 1
  have h1 : (f P).symm (fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - y0 P
      = (f P).symm ((fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - w P) := by
    rw [map_sub]; simp [w]
  rw [h1, hexp, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := hcr P j l
  have e2 := hwr P j
  simp only [M, map_mul, map_sub, map_pow, map_natCast, Pi.sub_apply]
  rw [e1, e2]
  have hq : ((qOf P.1 : ℕ) : E) ≠ 0 := by
    have := hN P
    intro h; apply this
    exact (IsFractionRing.injective (𝓞 E) E) (by rw [map_natCast, h, map_zero])
  field_simp

theorem approx_frames_target : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) :=
  fun E _ _ n SB f y0 e => approx_frames E n SB f y0 e

end GlobalTheory.CRTFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorSameCouplingCosetAllBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameCongApprox

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_val_le {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : P.valuation E a ≤ 1) : IntAt P a := by
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem exists_depth (P : HeightOneSpectrum (𝓞 E)) {w : 𝓞 E} (hw : w ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P (algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E w) := by
  have h0 : P.intValuation w ≠ 0 := P.intValuation_ne_zero w hw
  refine ⟨(P.intValuation w).log.natAbs, fun z hz => intAt_of_val_le ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_one₀ (zero_lt_iff.2 h0)]
  refine ((P.intValuation_le_pow_iff_mem z _).2 hz).trans ?_
  conv_rhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) (t : T → E) (u : T → 𝓞 E) (hu : ∀ P, u P ≠ 0) :
    ∃ y : E, ∀ P : T, IntAt P.1 ((y - t P) / algebraMap (𝓞 E) E (u P)) := by
  have inj := IsFractionRing.injective (𝓞 E) E
  choose a b hb hab using fun P => IsFractionRing.div_surjective (𝓞 E) (t P)
  have hb0 : ∀ P, b P ≠ 0 := fun P => nonZeroDivisors.ne_zero (hb P)
  set D : 𝓞 E := ∏ Q, b Q with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q
  have hw : ∀ P, D * u P ≠ 0 := fun P => mul_ne_zero hD0 (hu P)
  choose k hk using fun P : T => exists_depth P.1 (hw P)
  obtain ⟨x, hx⟩ := exists_forall_sub_mem_ideal (s := T) (fun P => P.asIdeal)
    (fun P => if h : P ∈ T then k ⟨P, h⟩ else 0) (fun P _ => P.prime)
    (fun P _ Q _ h h' => h (HeightOneSpectrum.ext h')) (fun P => a P * ∏ Q ∈ Finset.univ.erase P, b Q)
  refine ⟨algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E D, fun P => ?_⟩
  have hxP := hx P.1 P.2
  simp only [dif_pos P.2] at hxP
  have h1 := hk P _ hxP
  convert h1 using 1
  have hsplit : D = b P * ∏ Q ∈ Finset.univ.erase P, b Q := (Finset.mul_prod_erase _ _ (Finset.mem_univ P)).symm
  have hbE : algebraMap (𝓞 E) E (b P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hb0 P)
  have hBE : algebraMap (𝓞 E) E (∏ Q ∈ Finset.univ.erase P, b Q) ≠ 0 :=
    (map_ne_zero_iff _ inj).2 (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q)
  have huE : algebraMap (𝓞 E) E (u P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hu P)
  rw [← hab P, map_mul, map_sub, map_mul, hsplit, map_mul]
  field_simp

theorem exists_den {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ (P : HeightOneSpectrum (𝓞 E)) (z : Fin n → E), (∀ l, IntAt P (z l)) →
      ∀ l, IntAt P (algebraMap (𝓞 E) E d * g z l) := by
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => g (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun P z hz l => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ g z, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) fun j _ => ?_
  obtain ⟨r, hr⟩ := hdi (j, l) (Finset.mem_univ _)
  rw [Algebra.smul_def] at hr
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  exact (hz j).mul (by rw [← hr]; exact IntAt.coe P r)

end GlobalTheory.FrameCongApprox

namespace GlobalTheory.FrameCongApprox

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ}
    (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  have inj := IsFractionRing.injective (𝓞 X.E) X.E
  choose d hd0 hd using fun P : rowSG Pr sel mu => exists_den (fr P).symm.toLinearMap
  let e : rowSG Pr sel mu → ℕ := fun P => if P.1 ∈ Pr.vGs then 0 else cst.M
  let m : rowSG Pr sel mu → 𝓞 X.E := fun P => d P * ((qOf P.1 : ℕ) : 𝓞 X.E) ^ e P
  have hq : ∀ P : rowSG Pr sel mu, ((qOf P.1 : ℕ) : X.E) ≠ 0 := fun P => by
    rw [Nat.cast_ne_zero]
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hmE : ∀ P, algebraMap (𝓞 X.E) X.E (m P) = algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P := fun P => by
    simp [m, map_mul, map_pow, map_natCast]
  have hm : ∀ P, m P ≠ 0 := fun P h => by
    have h2 := hmE P
    rw [h, map_zero] at h2
    exact mul_ne_zero ((map_ne_zero_iff _ inj).2 (hd0 P)) (pow_ne_zero _ (hq P)) h2.symm
  choose yl hyl using fun l : Fin n => exists_approx (rowSG Pr sel mu) (fun P => fr P (y0 P) l) m hm
  refine ⟨yl, fun P l => ?_⟩
  have hmP : algebraMap (𝓞 X.E) X.E (m P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hm P)
  set z : Sp X.E n := fun l => (yl l - fr P (y0 P) l) / algebraMap (𝓞 X.E) X.E (m P) with hz
  have hy : yl = fr P (y0 P) + algebraMap (𝓞 X.E) X.E (m P) • z := by
    funext l
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdiff : (fr P).symm yl - y0 P = algebraMap (𝓞 X.E) X.E (m P) • (fr P).symm z := by
    rw [hy, map_add, map_smul, LinearEquiv.symm_apply_apply, add_sub_cancel_left]
  have key := hd P P.1 z (fun l => hyl l P) l
  show IntAt P.1 (((qOf P.1 : X.E) ^ e P)⁻¹ * ((fr P).symm yl - y0 P) l)
  rw [hdiff, Pi.smul_apply, smul_eq_mul, hmE]
  have : (((qOf P.1 : ℕ) : X.E) ^ e P)⁻¹ * (algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P * (fr P).symm z l) =
      algebraMap (𝓞 X.E) X.E (d P) * (fr P).symm.toLinearMap z l := by
    have hqe := pow_ne_zero (e P) (hq P)
    simp only [LinearEquiv.coe_coe]
    field_simp
  rw [this]
  exact key

end GlobalTheory.FrameCongApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BadPrimes

theorem mapPrime_conjugate {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    seamP s (conjPrime₂ P) = conjPrime₂ (seamP s P) := by
  apply HeightOneSpectrum.ext
  ext r
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
  have hc : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) :=
    RingOfIntegers.ext ((bridge_star_holds D.R D.host (s.iE x)).trans (hs.2 (x : X.E)).symm)
  rw [mem_conjP, hc, mem_seamP, mem_seamP, mem_conjP]

theorem lev_pos_and_noConj :
    UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie
  obtain ⟨hSS, hlev, -⟩ := (isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop
  refine ⟨?_, ?_⟩
  · rw [hlev]
    have hprod : 0 < ∏ P : rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 :=
      Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.mul_pos (pow_pos hprod _) (Nat.mul_pos (t.pr_ok.T_prime _).pos (pow_pos hprod _))
  · intro Q hQ hQ'
    obtain ⟨P, rfl⟩ : ∃ P, seamP t.seam P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).surjective Q
    rw [← mapPrime_conjugate t.seam t.seam_ok, mem_ssRec, hSS] at hQ'
    rw [mem_ssRec, hSS] at hQ
    exact sall_noConj t.sel (t.tup μ) hP.fields t.pr_ok hP.sel (t.word u) hP.avoid.2 hP.avoid.1 P hQ hQ'

end GlobalTheory.BadPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChanges
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_of_move : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  intro D cc a b SS cl N N' Ξ e e' he he' h x x' hx
  have hs : star e * e = 1 := mul_eq_one_comm.1 he
  have hs' : star e' * e' = 1 := mul_eq_one_comm.1 he'
  have hRR : ∀ y : HomE D.host.E a b, Matrix.toLin' (star e') ∘ₗ (KerMove.RR (star e) (star e') y) ∘ₗ Matrix.toLin' e = y := by
    intro y
    refine LinearMap.ext fun v => ?_
    simp only [KerMove.RR_apply, LinearMap.comp_apply, star_star]
    rw [← LinearMap.comp_apply (Matrix.toLin' (star e')) (Matrix.toLin' e'), ← Matrix.toLin'_mul, hs', Matrix.toLin'_one,
      LinearMap.id_apply, ← LinearMap.comp_apply (Matrix.toLin' (star e)) (Matrix.toLin' e), ← Matrix.toLin'_mul, hs,
      Matrix.toLin'_one, LinearMap.id_apply]
  have key := h (KerMove.RR (star e) (star e') x) (KerMove.RR (star e) (star e') x') (fun P hP => by
    have h1 := KerMove.localization_map₂ (D := D) (KerMove.RR (star e) (star e')) _ _
      (fun z hz => KerMove.perO_map (aaOf D cc) N (SDLat.smulLat e N) N' (SDLat.smulLat e' N') (KerMove.RR (star e) (star e'))
        (fun w hw => KerMove.homO_RR_inv e e' he N N' w hw) z hz) P _ (hx P hP)
    rwa [map_smul, map_sub] at h1)
  simpa only [hRR] using key

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepLevelLocalElementsValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levSrc_localData : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie hi β κ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid t.m2 hi le_rfl β
  have hκ := (((St t.m2 hi.le).K β).lev.U_eq κ.1).1 κ.2
  have key : ∀ P : SB t μ, ∃ g z, A.midRel t.m2 hi β P g z ∧
      InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 g := by
    intro P
    refine hLe P (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) ?_ κ.1 hκ.1 (hκ.2 _)
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g z hgz using key
  exact ⟨g, z, hgz, hChi κ g z hgz⟩

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalConditionInvariantRightLevelTranslate
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem funMoved_mul_level : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  intro D X s i hi T bad lev ST SG P v h ι x κ d
  unfold FunMoved
  intro H w hw z hz
  have hU := (lev.U_eq κ.1).1 κ.2
  have hk : bc (prV (E := D.host.E) v) κ.1 ∈ lev.Uloc v := hU.2 v
  rw [lev.UlocAlt v h] at hk
  have hk2 := (Subgroup.mem_inf.1 hk).2
  change ∃ _, _ at hk2
  obtain ⟨hst, hf⟩ := hk2
  have hp : pullV (F := D.host.F) (x * κ.1) (fun a => s.iE (w a)) =
      (κ.1⁻¹).val *ᵥ pullV (F := D.host.F) x (fun a => s.iE (w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hz1 : z.1 = (bc (prV (E := D.host.E) v) κ.1⁻¹).val *ᵥ
      (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) := by
    rw [hz, hp]
    funext l
    exact RingHom.map_mulVec _ _ _ l
  have hz0 : (bc (prV (E := D.host.E) v) κ.1).val *ᵥ z.1 =
      fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l) := by
    have e : (bc (prV (E := D.host.E) v) κ.1).val * (bc (prV (E := D.host.E) v) κ.1⁻¹).val = 1 := by
      rw [← Units.val_mul (bc (prV (E := D.host.E) v) κ.1), ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine (congrArg (fun y => (bc (prV (E := D.host.E) v) κ.1).val *ᵥ y) hz1).trans ?_
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  rw [H w hw ⟨_, (hst z.1).1 z.2⟩ hz0]
  exact congrArg ι (hf z)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeamTwist

theorem seamHom_smul {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : X.E) (x : HomE D.host.E a b) :
    seamHom s (s.iE r • x) = r • seamHom s x := by
  refine LinearMap.ext fun w => funext fun l => s.iE.injective ?_
  rw [seamHom_apply]
  show s.iE r * x (fun k => s.iE (w k)) l = s.iE (r * seamHom s x w l)
  rw [map_mul, seamHom_apply]

theorem seamHom_smul_int {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : 𝓞 X.E) (x : HomE D.host.E a b) :
    seamHom s (RingOfIntegers.mapRingEquiv s.iE r • x) = r • seamHom s x :=
  seamHom_smul s (r : X.E) x

theorem seamHom_mem_locP {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b))
    (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)) (h : ∀ x, seamHom s x ∈ M ↔ x ∈ M') (P : HeightOneSpectrum (𝓞 X.E))
    (x : HomE D.host.E a b) :
    seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
  show (∃ r ∈ P.asIdeal.primeCompl, r • seamHom s x ∈ M) ↔ ∃ r ∈ (seamP s P).asIdeal.primeCompl, r • x ∈ M'
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, fun hh => hr ((mem_seamP s P r).1 hh), (h _).1 ?_⟩
    rwa [seamHom_smul_int]
  · rintro ⟨r, hr, hm⟩
    obtain ⟨r, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
    refine ⟨r, fun hh => hr ((mem_seamP s P r).2 hh), ?_⟩
    rw [← seamHom_smul_int]
    exact (h _).2 hm

theorem seamHom_mem_twO : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  intro D X s a b M M' h cl e e' he x
  have key : ∀ P : HeightOneSpectrum (𝓞 X.E),
      ((cl : X.E) ^ e P)⁻¹ • seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔
        ((cl : D.host.E) ^ e' (seamP s P))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
    intro P
    rw [← seamHom_smul, seamHom_mem_locP s M M' h, he, map_inv₀, map_zpow₀, map_natCast]
  unfold twist₂
  rw [Submodule.mem_iInf, Submodule.mem_iInf]
  constructor
  · intro hx Q
    obtain ⟨P, rfl⟩ : ∃ P, seamP s P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).surjective Q
    exact (key P).1 (hx P)
  · intro hx P
    exact (key P).2 (hx (seamP s P))

end GlobalTheory.SeamTwist
end

