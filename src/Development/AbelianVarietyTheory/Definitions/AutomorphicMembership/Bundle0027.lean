import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
section
noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem g_big (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (g : ℕ), s.eps = eps → x0 ≤ s.x →
    RankVal s R → ((R.k : ℝ) * s.b) ^ 8 ≤ g → 2 * R.f * R.k < g - 1 := by
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 4 1 h0 one_pos
  refine ⟨max x3 (max x4 10), fun s R g he hx hR hg => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨y3, y4, y5⟩ := hx
  obtain ⟨hf, -⟩ := hx3 s R he y3 hR
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hk3 := R.m_add_three_le_k
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hb' : s.x ^ 4 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have h3 : 1 ≤ s.x ^ 3 := one_le_pow₀ (by linarith)
  have h4 : 10 * s.x ^ 3 ≤ s.b := by
    calc 10 * s.x ^ 3 ≤ s.x * s.x ^ 3 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 4 := by ring
      _ ≤ s.b := hb'
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have c1 : (R.k : ℝ) * s.b ≤ g :=
    (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 (by linarith)) (by norm_num)).trans hg
  have c3 : ((2 * R.f * R.k + 1 : ℕ) : ℝ) < g := by
    have d1 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ R.k by positivity)
    have d2 := mul_le_mul_of_nonneg_left hf' (show (0 : ℝ) ≤ R.k by positivity)
    have d3 := one_le_mul_of_one_le_of_one_le hk1 h3
    push_cast
    nlinarith
  have c4 : 2 * R.f * R.k + 1 < g := by exact_mod_cast c3
  omega

set_option maxHeartbeats 1000000 in

theorem not_ev_false (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM) : ¬ Ev fun _ => False := by
  rintro ⟨ε0, hε0, h⟩
  have he : 0 < min ε0 (1 / 100) := lt_min hε0 (by norm_num)
  have he52 : min ε0 (1 / 100) < 1 / 52 := (min_le_right _ _).trans_lt (by norm_num)
  have hle := min_le_left ε0 (1 / 100)
  generalize min ε0 (1 / 100) = eps at he he52 hle
  obtain ⟨la, hla, hH⟩ := hH
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, -, -, -, S, hH⟩ := hH eps he he52
  obtain ⟨K0, h⟩ := h eps C8 he hle he52 h8
  obtain ⟨C, hS, hCT, hCp, hL, -⟩ := GlobalTheory.EX.exists_std_large K0 K0 CT2 C8 h8
  obtain ⟨c1, h⟩ := h C hS hCp hL
  have hcD : 0 ≤ max c1 0 := le_max_right _ _
  obtain ⟨c2, h⟩ := h _ (le_max_left c1 0)
  generalize max c1 0 = cD at hcD h
  obtain ⟨c2', hlow⟩ := WinLow.window_lower h2b eps C he he52 hS cD hcD
  obtain ⟨ch, a1, a2, a3⟩ : ∃ ch : ℝ, c2 ≤ ch ∧ c2' ≤ ch ∧ 402 ≤ ch := ⟨max c2 (max c2' 402), by simp, by simp, by simp⟩
  obtain ⟨x0, h⟩ := h ch a1
  obtain ⟨x1, hlow⟩ := hlow ch a2
  have hmid := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hS
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x2, h2⟩ := chOK_of_host hSP eps C5 c6 Cb cD ch C he he52 hS hcD a3
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps 1 C he he52 one_pos hS
  obtain ⟨x4, h4⟩ := g_big eps he he52
  obtain ⟨s, hs, hx, hmem⟩ := S.exists_mem hla.le he he52
    (max x0 (max x1 (max x2 (max x3 (max x4 (max xH (max xw xc)))))))
  simp only [max_le_iff] at hx
  obtain ⟨b0, b1, b2, b3, b4, bH, bw, bc⟩ := hx
  obtain ⟨R, H, q0, hRV, hHT, hHG, -⟩ := hH s hs bH hmem
  obtain ⟨a, b, hab⟩ := hw s R H hs bw hRV
  obtain ⟨c, hci, -⟩ := hc s R hs bc hRV
  obtain ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, -⟩ :=
    h2 s R H q0 a b _ c 0 hs b2 hRV (hHT.trans hCT.symm) (hCp ▸ hHG) hab rfl hci R.ord_pos
  choose du hpos hdu using fun u => DuInt.duStarOf_nat R H' (hcW u) (fun i => (k2 _ (H'.g_level i)).2)
    fun i => h4 s R _ hs b4 hRV (hCh.val.2.2.2.2.1 i).1
  obtain ⟨hD, hDle⟩ := DsLow.DsP_pos_and_lower (@PreCh.mk R H' k1 k2 k3 _ _ w0 hcW k4 k5 k6 k7 k8)
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ q1 a b c du _ hs b3 hCh hpos hD fun u => by
    rw [one_mul]
    exact hlow s _ q1 a b c du _ hs b1 hCh hdu hDle u
  exact h ⟨s, C, cD, ch, _, q1, a, b, c, hS, hCh, Lv, fun u => by rw [l1]; exact hdu u, l2, l3⟩ rfl rfl rfl hs b0

end GlobalTheory.Mem.Top.Inh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
section
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def IsTw : Prop := ∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧
  I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)

@[reducible] def canon : TC B X :=
  { I with
    cst := fun a => twCst I.Ch I.sel (I.tup a) I.glob
    idx := fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) }

theorem canon_isTw : I.canon.IsTw := fun _ => ⟨rfl, rfl⟩

abbrev idxFull (a : I.ι) : ChIdx B.fields (B.primes X) B.R (I.Q a) :=
  (I.idx a).withTop (B.R.m - 2) (twLt I.Ch) (twTt I.sel (I.tup a))

def Deep : Prop := ∀ a (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∉ (B.primes X).vGs → 2 * B.R.m ≤ (I.cst a).D P

variable {I}

theorem IsTw.cst_eq (h : I.IsTw) (a : I.ι) : I.cst a = twCst I.Ch I.sel (I.tup a) I.glob := (h a).1

theorem IsTw.idx_eq (h : I.IsTw) (a : I.ι) :
    I.idx a = twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) := by
  rw [(h a).2, (h a).1]

theorem IsTw.idxFull_eq (h : I.IsTw) (a : I.ι) :
    I.idxFull a = twIdxTop I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2) (twLt I.Ch) (twTt I.sel (I.tup a)) := by
  unfold idxFull
  rw [(h a).2]
  rfl

theorem isTw_iff_canon_eq : I.IsTw ↔ I.canon = I := by
  refine ⟨fun h => ?_, fun h => h ▸ I.canon_isTw⟩
  have h1 : (fun a => twCst I.Ch I.sel (I.tup a) I.glob) = I.cst := funext fun a => (h.cst_eq a).symm
  have h2 : (fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)) = I.idx :=
    funext fun a => (h.idx_eq a).symm
  unfold canon
  rw [h2, h1]

theorem IsTw.deep (h : I.IsTw) : I.Deep := fun a P hP => by
  rw [h.cst_eq a, twCst_D_Q hP]

theorem qOf_mod_four (B : Base) (X : PreX B.toPre) : ∀ w ∈ (B.primes X).vGs, qOf w % 4 = 1 := fun w hw => by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨k, hk⟩ : ∃ k, w ∈ (B.primes X).vG k := by
    classical
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  rw [show qOf w = (B.primes X).g k from hPr.vG_norm k w hk]
  exact (hPr.g_cong k).of_dvd (by
    show 4 ∣ B.host.QS * B.host.q * B.host.d
    exact (((pow_dvd_pow 2 (Nat.le_add_left 2 B.R.e) : 2 ^ 2 ∣ 2 ^ (B.R.e + 2)).trans B.host.tower_dvd).mul_right _).mul_right _)

theorem val_of_ok (h : I.Ok) (j : Fin B.R.m) (w : HeightOneSpectrum (𝓞 B.fields.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ y : B.fields.K, I.glob.σ₀ y = ((((I.glob.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hq : (qOf w : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  have e := (h.idx_ok I.mu0).muqG j j.2 ⟨w, Finset.mem_union_left _ hw⟩ hw (ciQU w) (by simp [ciQU, hq])
  refine ⟨(I.cst I.mu0).muq (j + 1) ⟨w, Finset.mem_union_left _ hw⟩ *
    (qValC (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) w : B.fields.Kˣ), ?_⟩
  rw [map_mul, e, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem Q_notMem_of_ok (h : I.Ok) (a : I.ι) : ∀ P ∈ I.Q a, P ∉ (B.primes X).vGs := fun _ hP =>
  IdxEx.notMem_vGs_of_mem_QE (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok h.g_mem (I.tup a) hP

theorem degOne_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : TwDegOne B.fields P.1 :=
  degOneUnram_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok (I.tup a) P

theorem sqrt_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : ∃ z : B.fields.K, z ^ 2 = (qOf P.1 : B.fields.K) :=
  ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩

theorem root_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs) :
    ∃ z : B.fields.K, I.glob.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * B.R.m) : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hD a P hP)
  have hq : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hqC : (qOf P.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  obtain ⟨x1, x2⟩ := (h.idx_ok a).xiUnitAtPrime P
  have hx : I.glob.xi0 ≠ 0 := fun e => x2 (e ▸ redP_zero)
  have hi : IntAt P.1 ((qOf P.1 ^ k : ℕ) : B.fields.E) := by
    simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 ((qOf P.1 ^ k : ℕ) : ℤ)
  have e := (h.idx_ok a).weil P (I.glob.xi0⁻¹ / (qOf P.1 : B.fields.E) ^ (2 * B.R.m)) ((qOf P.1 ^ k : ℕ) : ℤ)
    (by
      convert hi.mul (yIntAt_inv x1 x2) using 1
      rw [hk]; push_cast; field_simp; ring)
    (by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 0 using 1
      rw [hk]; push_cast; field_simp; ring)
  refine ⟨_, e.trans ?_⟩
  congr 1
  rw [hk]; push_cast; field_simp; ring

theorem twIdx_ok_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) :
    (twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)).Ok I.Ch I.sel (I.tup a)
      (twCst I.Ch I.sel (I.tup a) I.glob) I.glob (B.R.m - 2) :=
  twIdx_ok_closed (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok (qOf_mod_four B X) I.glob
    h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a)
    (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)

theorem canon_ok (h : I.Ok) (hD : I.Deep) : I.canon.Ok :=
  { h with sharp := fun _ => rfl, idx_ok := twIdx_ok_of_ok (I := I) h hD }

theorem IsTw.chF_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idx a) u j).Ok := by
  have ho : ∀ b, ThetaOpen ((I.idx a).levQ j b) := by
    rw [(ht a).2]
    exact thetaOpen_twIdx I.Ch I.sel (I.tup a) (I.cst a) (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ j
  exact chF_ok_of_finIdx W I.sel (I.tup a) _ (base_fields_primes_ok B X).1 u j
    (fun b P => thetaOpen_finIdx _ (ho b) P) (fun b c => thetaOpen_root _ (ho b) c)

theorem IsTw.chF_full_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idxFull a) u j).Ok := by
  rw [ht.idxFull_eq]
  exact twTop_chF_ok I.Ch I.sel (I.tup a) W (base_fields_primes_ok B X).1 (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ u j

example (h : I.IsTw) (a : I.ι) : (I.cst a).sharp = true ∧ (I.cst a).M = B.R.m := by
  rw [h.cst_eq a]; exact ⟨rfl, rfl⟩

example (a : I.ι) (h : (I.cst a).sharp = false) : ¬ I.IsTw := fun ht => by
  rw [ht.cst_eq a] at h; exact Bool.noConfusion h

example : I.canon.C = I.C ∧ I.canon.xi = I.xi ∧ I.canon.glob = I.glob := ⟨rfl, rfl, rfl⟩

end GlobalTheory.Mem.Col2.TC

end
end

