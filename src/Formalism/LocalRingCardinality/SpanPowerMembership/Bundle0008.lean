import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0007
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeF
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeG

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  Eff := fun Y => Empty.elim Y
  eff_zero := fun Y => Empty.elim Y
  eff_add := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  degreeZeroCohomology_finiteDimensional := fun Y => Empty.elim Y
  mul_mem_riemannRochSpace_add := fun Y => Empty.elim Y
  riemannRoch_mono := fun Y => Empty.elim Y
  KY := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  properCl := fun Y => Empty.elim Y
  subCl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  nef := fun Y => Empty.elim Y
  big := fun Y => Empty.elim Y
  bpf := fun Y => Empty.elim Y
  phiBir := fun Y => Empty.elim Y
  phiNoContr := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  hdim := fun Y => Empty.elim Y
  pts := fun Y => Empty.elim Y
  ptsMeas := fun Y => Empty.elim Y
  vol := fun Y => Empty.elim Y
  FnC := fun Y => Empty.elim Y
  fnCRing := fun Y => Empty.elim Y
  fnCAlg := fun Y => Empty.elim Y
  cx := fun Y => Empty.elim Y
  cx_smul := fun Y => Empty.elim Y
  Met := fun Y => Empty.elim Y
  mAdd := fun Y => Empty.elim Y
  mPow := fun Y => Empty.elim Y
  fsMet := fun Y => Empty.elim Y
  pn := fun Y => Empty.elim Y
  pnK := fun Y => Empty.elim Y
  mSmooth := fun Y => Empty.elim Y
  mPsh := fun Y => Empty.elim Y
  redZero := fun Y => Empty.elim Y
  agreeOn := fun Y => Empty.elim Y
  resNorm := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y
  supInf := fun Y => Empty.elim Y
  supFin := fun Y => Empty.elim Y
  cutGood := fun Y => Empty.elim Y
  cutHt := fun Y => Empty.elim Y
  cutOrd := fun Y => Empty.elim Y
  resFull := fun Y => Empty.elim Y
  resDeg := fun Y => Empty.elim Y
  supInf_ofW := fun Y => Empty.elim Y
  supInf_twist := fun Y => Empty.elim Y
  supFin_twist := fun Y => Empty.elim Y
  regOn := fun Y => Empty.elim Y

variable (D : D7)

def divXExample (_h0 : D.what₂.Drows = 0) (hM : ∀ j, Subsingleton (D.what₂.Mj j)) : DivX D where
  geo := geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}
  plpFin := fun p _ => PlOver.plFin D p
  plpNe := fun p _ => PlOver.plNe D p
  wtP := fun p _ la => PlOver.wt D p la.1
  divisorWeight_nonneg := fun p _ la => PlOver.wt_nonneg D p la.1
  divisorWeight_sum := fun p _ => PlOver.wt_sum D p
  plP := fun _ _ => Equiv.refl _
  divisorWeight_def := fun _ _ _ => rfl
  jC := fun p _ _ => (teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := fun _ => zeroHLat _
  MjH_good := fun _ => zeroHLat_good _
  jM := fun _ => 0
  jM_basis := fun j => by
    have := hM j
    exact ⟨linearIndependent_empty_type (ι := Fin 0), Subsingleton.elim _ _⟩
  jM_lat := fun j _ _ _ => by
    have := hM j
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Submodule.mem_top⟩
  jM_metric := fun _ _ _ _ => (normAt_empty (ι := Fin 0) _ _ _ _).trans norm_zero.symm
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  logLam_base := fun _ _ => rfl
  kapR := fun _ => 1
  kapR_pos := fun _ => one_pos
  kapR_conj := fun _ => rfl
  MjLat_sub := fun j _ _ _ _ => by
    have := hM j
    exact ⟨0, Subsingleton.elim _ _⟩
  phiFr_unram := fun _ κ => κ.elim
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.GatAdd
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

def tau1P (φ : Formalism.HC.Frame) (t : φ.A) : ↥φ.Psi := ⟨φ.tau1 t, rfl⟩

theorem tau1P_injective (φ : Formalism.HC.Frame) : Function.Injective (tau1P φ) := fun _ _ h =>
  φ.tau1_injective (congrArg Subtype.val h)

theorem iotaH_nsmul (φ : Formalism.HC.Frame) (t h : φ.A) (s : ℕ) :
    φ.iota (t + s • h) = φ.iota t * φ.iota h ^ s := rfl

def iotaHom (φ : Formalism.HC.Frame) : Multiplicative φ.A →* φ.MA where
  toFun x := φ.iota x.toAdd
  map_one' := φ.iota_zero
  map_mul' x y := φ.iota_add x.toAdd y.toAdd

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (h : φ.A) : orderOf (φ.iota h) = addOrderOf h := φ.orderOf_iota h

variable (D : D7) {p : ℕ}

theorem iotaH_hP (S : Served D.host p) :
    D.R.iota (hP D p) = hOf D.host p := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := exists_frob D.host p S.prime S.cls
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have hv := @frob_val _ D.host p S.prime S.cls P₂ h1 h2 σ₂ hσ₂
  unfold hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← he, hv]

theorem tau1P_mul_gPsi_pow (S : Served D.host p) (t0 : HH D) (s : ℕ) :
    tau1P D.R.toFrame t0 * gPsi S ^ s = tau1P D.R.toFrame (t0 + s • hP D p) := by
  apply Subtype.ext
  have hg : ((gPsi S ^ s : ↥(D.R.Psi)) : D.R.GG) =
      (1, hOf D.host p ^ s) := by
    unfold gPsi
    rw [← map_pow]
    rfl
  show D.R.tau1 t0 * ((gPsi S ^ s : ↥(D.R.Psi)) : D.R.GG) = D.R.tau1 (t0 + s • hP D p)
  unfold Formalism.HC.Frame.tau1
  rw [hg, Prod.mk_mul_mk, mul_one, iotaH_nsmul, iotaH_hP D S]

theorem order_gPsi (S : Served D.host p) : orderOf (gPsi S) = addOrderOf (hP D p) := by
  rw [(ord_spec S).1, ← iotaH_hP D S, orderOf_iotaH]

theorem injOn_tau1P (S : Served D.host p) (B : Set (HH D))
    (hB : ∀ t ∈ B, ∀ t' ∈ B, ∀ i : ℕ, t' = t + i • hP D p → t' = t) :
    Set.InjOn (fun x => (QuotientGroup.mk x : Quo (gPsi S))) (tau1P D.R.toFrame '' B) := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ h
  have h1 : (tau1P D.R.toFrame t)⁻¹ * tau1P D.R.toFrame t' ∈ Subgroup.zpowers (gPsi S) := QuotientGroup.eq.mp h
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨i, hi⟩ := h1
  have h2 : tau1P D.R.toFrame t' = tau1P D.R.toFrame t * gPsi S ^ i := by
    have hi' : gPsi S ^ i = (tau1P D.R.toFrame t)⁻¹ * tau1P D.R.toFrame t' := hi
    rw [hi', mul_inv_cancel_left]
  rw [tau1P_mul_gPsi_pow] at h2
  rw [hB t ht t' ht' i (tau1P_injective _ h2)]

variable (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (rOf : D.what₂.Word → ℕ → ℕ)
  (B : D.what₂.Word → ℕ → Set (HH D))

def withGatB : D7 := withGat D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p)

def gatTiesB : GatTies (withGatB D h0 rOf B) := gatTies D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p)

def vOfB (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : HH D) :
    Fin ((withGatB D h0 rOf B).gat u w h).P.nV :=
  orbIdx (gPsi (H := D.host) (served_of h)) (tau1P D.R.toFrame t0)

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem vOfB_injOn
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t) :
    Set.InjOn (vOfB D h0 rOf B u w h) (B u (D.what₂.places.resChar w)) := fun t ht t' ht' e =>
  tau1P_injective _ (orbIdx_injOn _ _ (injOn_tau1P D (served_of h) _ hB) ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩ e)

theorem withGatB_n' (v) :
    ((withGatB D h0 rOf B).gat u w h).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) :=
  order_gPsi D (served_of h)

theorem withGatB_r : ((withGatB D h0 rOf B).gat u w h).P.r = rOf u (D.what₂.places.resChar w) := rfl

theorem gatTiesB_pos
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t)
    {t0 : HH D} (ht0 : t0 ∈ B u (D.what₂.places.resChar w))
    (s : Fin (((withGatB D h0 rOf B).gat u w h).P.n' (vOfB D h0 rOf B u w h t0))) :
    ((D.eTau ((gatTiesB D h0 rOf B).gat_pos u w h ⟨vOfB D h0 rOf B u w h t0, s⟩) : D.R.Psi) :
      D.R.GG) = D.R.tau1 (t0 + s.val • hP D (D.what₂.places.resChar w)) := by
  have h1 := gatTies_pos_base D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p) u w h
    (injOn_tau1P D (served_of h) _ hB) ⟨t0, ht0, rfl⟩ s
  exact congrArg (fun x : ↥(D.R.Psi) => (x : D.R.GG))
    (h1.trans (tau1P_mul_gPsi_pow D (served_of h) t0 s.val))

theorem hP_withGatB (p : ℕ) : hP (withGatB D h0 rOf B) p = hP D p := rfl

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

structure Lbl where
  fA : ∀ k, (ZMod (H.g k))[X]
  fB : ∀ k, (ZMod (H.g k))[X]
  ne : ∀ k, fA k ≠ fB k
  okA : ∀ k, (fA k).Monic ∧ (fA k).natDegree = R.r ∧ (fA k).coeff 0 ≠ 0
  okB : ∀ k, (fB k).Monic ∧ (fB k).natDegree = R.r ∧ (fB k).coeff 0 ≠ 0
  good : ∀ k (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => if t v then fA k else fB k) (fun (_ : PP) (_ : J) => (1 : (ZMod (H.g k))ˣ))

theorem lbl_nonempty (ht : THyp H) (p : ℕ) (hp : p.Prime) (h1 : R.r < 2 * p) (h2 : p + 3 ≤ R.r) :
    Nonempty (Lbl H) := by
  have hd : ∀ k, H.QS * H.q * H.d ∣ H.g k - 1 := fun k => by
    have h := Nat.div_add_mod (H.g k) (H.QS * H.q * H.d)
    rw [ht.cond k] at h
    exact ⟨H.g k / (H.QS * H.q * H.d), by omega⟩
  have hq2 : H.q ≠ 2 := fun e => by have := H.hyp.2.2.1; omega
  have key := fun k => exists_good (g := H.g k) R.r p H.q hp h1 h2 H.hyp.1 hq2
    (((((dvd_pow_self 2 (by omega)).trans H.tower_dvd : 2 ∣ H.QS).mul_right H.q).mul_right H.d).trans (hd k))
    ((Dvd.intro (H.QS * H.d) (by ring)).trans (hd k))
  choose fA fB h using key
  exact ⟨⟨fA, fB, fun k => (h k).1, fun k => (h k).2.1, fun k => (h k).2.2.1, fun k => (h k).2.2.2⟩⟩

variable {H} (Lb : Lbl H)

def tupL (k : Fin 2) (v : Fin R.f) : (ZMod (H.g k))[X] := if decide (v.1 ≠ 0) then Lb.fA k else Lb.fB k

theorem two_le_f (R : Ranks) : 2 ≤ R.f := by
  have : 0 < R.n := by unfold Ranks.n; positivity
  unfold Ranks.f; omega

theorem tupL_good (J : Type) (k : Fin 2) :
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (tupL Lb k) (fun (_ : Fin R.f) (_ : J) => (1 : (ZMod (H.g k))ˣ)) :=
  Lb.good k (Fin R.f) J (fun v => decide (v.1 ≠ 0)) ⟨⟨1, two_le_f R⟩, by simp⟩
    ⟨⟨0, by have := two_le_f R; omega⟩, by simp⟩

def labL {FT : Type} (k : Fin 2) (_ : FT) (v : Fin R.f) : (ZMod (H.g k))[X] := tupL Lb k v

theorem labL_monic {FT : Type} (k : Fin 2) (σ : FT) (v : Fin R.f) :
    (labL Lb k σ v).Monic ∧ (labL Lb k σ v).natDegree = R.r := by
  unfold labL tupL
  split_ifs
  · exact ⟨(Lb.okA k).1, (Lb.okA k).2.1⟩
  · exact ⟨(Lb.okB k).1, (Lb.okB k).2.1⟩

variable (H) in

def zL (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) := -1

variable (H) in
theorem zL_ne_one (ht : THyp H) (k : Fin 2) : zL H k ≠ 1 := by
  intro h
  have hr : 0 < R.r := Nat.pos_of_ne_zero (r_ne_zero R)
  have h1 := congrArg (fun u : GL (Fin R.r) (ZMod (H.g k)) => (u : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k))) ⟨0, hr⟩ ⟨0, hr⟩) h
  simp only [zL, Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
  have h2 : (2 : ZMod (H.g k)) = 0 := by linear_combination -h1
  have h3 : ((2 : ℕ) : ZMod (H.g k)) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact (ht.jac k).1 ((Nat.prime_dvd_prime_iff_eq (H.g_prime k) Nat.prime_two).mp h3)

def esL (K : Type) [Field K] (k : Fin 2) : (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))) :=
  esZ K (GL (Fin R.r) (ZMod (H.g k))) (Lb.fA k) (Lb.fB k)

variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

abbrev ndG : NData R H what₂ := ndL H what₂ h (labL Lb) (labL_monic Lb)

theorem goodT_tupL : GoodT (ndG H Lb what₂ h) (tupL Lb) := fun k =>
  ⟨tupL_good Lb _ k, by
    have e : (fun (v : Fin R.f) (j : Fin R.m) => ((1 : (ZMod (H.g k))ˣ))⁻¹) = fun _ _ => 1 := by
      funext _ _; exact inv_one
    show Formalism.CyclotomicNorms.IsGood R.r (H.g k) (tupL Lb k) (fun (v : Fin R.f) (j : Fin R.m) => ((1 : (ZMod (H.g k))ˣ))⁻¹)
    rw [e]; exact tupL_good Lb _ k⟩

theorem goodRow_ndG (σ : what₂.FT) : (ndG H Lb what₂ h).goodRow σ := goodT_tupL H Lb what₂ h

section Field

variable (K : Type) [Field K] [CharZero K]

def e0L : MonoidAlgebra K (G0g (ndG H Lb what₂ h)) := e0F (ndG H Lb what₂ h) (esL Lb K)

theorem labelIdempotent_idem : e0L H Lb what₂ h K * e0L H Lb what₂ h K = e0L H Lb what₂ h K :=
  seriesIdempotent_idem _ _ (fun k f => esZ_idem f) (fun k f f' hf => esZ_orth f f' hf)

theorem labelIdempotent_central (a) : e0L H Lb what₂ h K * a = a * e0L H Lb what₂ h K :=
  seriesIdempotent_central _ _ (fun k f a => esZ_central f a) a

theorem labelIdempotent_ne_zero (ht : THyp H) : e0L H Lb what₂ h K ≠ 0 :=
  seriesIdempotent_ne_zero _ _ (fun k f => esZ_idem f) (fun k f f' hf => esZ_orth f f' hf)
    (tupL Lb) (goodT_tupL H Lb what₂ h) (fun k v => by
      unfold esL esZ tupL
      by_cases hv : decide (v.1 ≠ 0) = true
      · rw [if_pos hv, if_pos rfl]; exact one_sub_eT_ne_zero (zL H k) (zL_ne_one H ht k)
      · rw [if_neg hv, if_neg (Lb.ne k).symm, if_pos rfl]; exact eT_ne_zero)

def qcL (g : G0g (ndG H Lb what₂ h)) : ℚ := (e0L H Lb what₂ h ℚ).coeff g

theorem labelIdempotent_coeff (g) : (e0L H Lb what₂ h K).coeff g = (qcL H Lb what₂ h g : K) := by
  unfold qcL e0L e0F
  rw [eSum_coeff, eSum_coeff, Rat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    show (esZ K _ _ _ _).coeff _ = ((esZ ℚ _ _ _ _).coeff _ : K)
    rw [esZ_coeff, esZ_coeff, Rat.cast_id]
  · simp

end Field

theorem labelIdempotent_mem_center : e0L H Lb what₂ h ℂ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) :=
  Subalgebra.mem_center_iff.mpr fun b => (labelIdempotent_central H Lb what₂ h ℂ b).symm

def omL (ht : THyp H) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) →ₐ[ℂ] ℂ :=
  (exists_char _ (labelIdempotent_mem_center H Lb what₂ h) (labelIdempotent_idem H Lb what₂ h ℂ) (labelIdempotent_ne_zero H Lb what₂ h ℂ ht)).choose

theorem labelCharacter_idempotent_one (ht : THyp H) : omL H Lb what₂ h ht ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ = 1 :=
  (exists_char _ (labelIdempotent_mem_center H Lb what₂ h) (labelIdempotent_idem H Lb what₂ h ℂ) (labelIdempotent_ne_zero H Lb what₂ h ℂ ht)).choose_spec

set_option synthInstance.maxHeartbeats 400000 in

def ntypesL (ht : THyp H) (htm : TameHyp H) : NTypes (nautL H what₂ h (labL Lb) (labL_monic Lb)) where
  Mray := H.E
  Mray_gal := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  Mray_ab := galK_comm H
  Mray_unr := discr_prime H
  g_Mray := h.hg
  g_cond := ht.cond
  BB_disj := ht.bb
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    rw [Multiset.mem_singleton.mp hp]; exact ⟨Nat.pos_of_ne_zero (r_ne_zero R), one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by simp
  tg := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose
  tg_mem := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose_spec.1
  tg_gen := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose_spec
  inertiaCharpoly_type := fun k v L hL => by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have h0 : Multiset.card (L : Multiset ℂˣ) = 0 := hL.symm.trans natDegree_one
    show (X - 1 : ℂ[X]) ^ Multiset.card (L : Multiset ℂˣ) =
      ((Formalism.CyclotomicNorms.rootsBar (1 : (ZMod (H.g k))[X])).map fun x => X - C (@teichToC (H.g k) ⟨H.g_prime k⟩ x)).prod
    rw [h0]
    simp [Formalism.CyclotomicNorms.rootsBar]
  chiT_tg := fun i => i.elim
  heckeLoc_gamma_places := fun i => i.elim
  iota := fun k _ w => @teichIota (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩
  iota_inj := fun k _ w => @teichIota_inj (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩
    ⟨what₂.places.resChar_prime w⟩
  teichC := fun k => @teichToC (H.g k) ⟨H.g_prime k⟩
  teichC_inj := fun k _ _ _ _ e => @teichToC_injective (H.g k) ⟨H.g_prime k⟩ _ _ e
  eSer := esL Lb ℂ
  eSer_idem := fun k f => esZ_idem (K := ℂ) f
  eSer_central := fun k f a => esZ_central (K := ℂ) f a
  eSer_orth := fun k f f' hff => esZ_orth (K := ℂ) f f' hff
  eSer_zero := fun k f hf => by
    unfold esL esZ
    rw [if_neg (fun e : f = Lb.fA k => hf (e ▸ Lb.okA k)), if_neg (fun e : f = Lb.fB k => hf (e ▸ Lb.okB k))]
  eSer_sum := fun k => by
    have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
    have hfin : {f : (ZMod (H.g k))[X] | f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0}.Finite := by
      apply (Set.finite_range (fun a : Fin R.r → ZMod (H.g k) => Formalism.CyclotomicNorms.monicOf a)).subset
      rintro f ⟨hm, hd, -⟩
      exact ⟨fun i => f.coeff i, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
    exact ⟨hfin.toFinset, fun f => by simp, esZ_sum (K := ℂ) (Lb.ne k) _ (by simpa using Lb.okA k)
      (by simpa using Lb.okB k)⟩
  cenAmb := fun μ => (Algebra.ofId ℂ (Module.End ℂ (what₂.Amb μ))).comp (omL H Lb what₂ h ht)
  cenMt := fun μ j => (Algebra.ofId ℂ (Module.End ℂ (what₂.Mt μ j))).comp (omL H Lb what₂ h ht)
  Par := Empty
  labPar := fun _ σ => σ.elim
  labPar_monic := fun _ σ => σ.elim
  locPar := fun σ => σ.elim
  locPar_dim := fun σ => σ.elim
  labPar_def := fun _ σ => σ.elim
  MtPar := fun _ _ σ => σ.elim
  AmbPar := fun _ σ => σ.elim

theorem labelNewtypes_idempotent_eq (ht htm) : (ntypesL H Lb what₂ h ht htm).e0 = e0L H Lb what₂ h ℂ := e0_eq _

theorem labelNewtypes_idempotent_ne_zero (ht htm) : (ntypesL H Lb what₂ h ht htm).e0 ≠ 0 := by
  rw [labelNewtypes_idempotent_eq]; exact labelIdempotent_ne_zero H Lb what₂ h ℂ ht

theorem ntypesL_E0Tie (ht htm) (hA : ∀ μ, what₂.eOp μ = 1) (hM : ∀ μ j, what₂.eMt μ j = 1) :
    (ntypesL H Lb what₂ h ht htm).IdempotentMatchesAction := by
  have key : (⟨(ntypesL H Lb what₂ h ht htm).e0, idempotent_mem_center _⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h)))) = ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ :=
    Subtype.ext (labelNewtypes_idempotent_eq H Lb what₂ h ht htm)
  refine ⟨fun μ => ?_, fun μ j => ?_⟩
  · rw [hA, ambientAction_idempotent, key]
    show (1 : Module.End ℂ (what₂.Amb μ)) = Algebra.ofId ℂ _ (omL H Lb what₂ h ht _)
    rw [labelCharacter_idempotent_one, map_one]
  · rw [hM, matrixAction_idempotent, key]
    show (1 : Module.End ℂ (what₂.Mt μ j)) = Algebra.ofId ℂ _ (omL H Lb what₂ h ht _)
    rw [labelCharacter_idempotent_one, map_one]

theorem labelIdempotent_baseField [NumberField what₂.LL] (LL0 : IntermediateField ℚ what₂.LL) (ht htm) (g) :
    what₂.embLL (((qcL H Lb what₂ h g : ℚ) : ↥LL0) : what₂.LL) = (ntypesL H Lb what₂ h ht htm).e0.coeff g := by
  rw [labelNewtypes_idempotent_eq, labelIdempotent_coeff]
  simp

end Formalism.BasicNotions.Examples₂.NZ
end
end

