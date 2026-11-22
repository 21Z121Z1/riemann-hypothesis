import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
open GlobalTheory.IdealTransport GlobalTheory.InertSign GlobalTheory.ThetaLatImage

noncomputable section

namespace GlobalTheory.PeriodTransport

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n a b : ℕ}

def vecT (n : ℕ) : (Fin n → E) ≃+ (Fin n → E') := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vecT_smul (r : 𝓞 E) (x : Fin n → E) : vecT e n (r • x) = RingOfIntegers.mapRingEquiv e r • vecT e n x :=
  funext fun i => map_smul_int e r (x i)

theorem trL_fg {N : Submodule (𝓞 E) (Fin n → E)} (h : N.FG) : (trL e N).FG := by
  obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 h
  exact Submodule.fg_def.2 ⟨_, hS.image (vecT e n),
    (span_image_span (RingOfIntegers.mapRingEquiv e) (vecT e n) (vecT_smul e) S).symm⟩

theorem trL_span {N : Submodule (𝓞 E) (Fin n → E)} (h : Submodule.span E (N : Set (Fin n → E)) = ⊤) :
    Submodule.span E' (trL e N : Set (Fin n → E')) = ⊤ := by
  have h1 := span_image_span e (vecT e n) (fun r x => funext fun i => map_mul e r (x i)) (N : Set (Fin n → E))
  rw [h, Submodule.top_coe, Set.image_univ, (vecT e n).surjective.range_eq, Submodule.span_univ] at h1
  refine top_le_iff.1 (h1.le.trans (Submodule.span_mono ?_))
  exact Submodule.subset_span

def matT (a b : ℕ) : HomE E a b ≃+ Matrix (Fin b) (Fin a) E' :=
  (LinearMap.toMatrix' (R := E) (m := Fin b) (n := Fin a)).toAddEquiv.trans e.toAddEquiv.mapMatrix

theorem matT_apply (x : HomE E a b) (i : Fin b) (j : Fin a) : matT e a b x i j = e (x (Pi.single j 1) i) := by
  change e (LinearMap.toMatrix' x i j) = _
  rw [LinearMap.toMatrix'_apply]

theorem matT_smul (r : E) (x : HomE E a b) : matT e a b (r • x) = e r • matT e a b x := by
  ext i j
  simp [matT_apply]

theorem matT_smul_int (r : 𝓞 E) (x : HomE E a b) :
    matT e a b (r • x) = RingOfIntegers.mapRingEquiv e r • matT e a b x := by
  ext i j
  rw [Matrix.smul_apply, matT_apply, matT_apply, ← map_smul_int]
  rfl

theorem matT_mulVec (x : HomE E a b) (v : Fin a → E') :
    (fun i => e.symm ((matT e a b x).mulVec v i)) = x fun j => e.symm (v j) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matT_apply]

theorem matT_carries (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) (x : HomE E a b) :
    (∀ v ∈ trL e N, (matT e a b x).mulVec v ∈ trL e N') ↔ ∀ y ∈ N, x y ∈ N' := by
  simp only [mem_trL, matT_mulVec]
  refine ⟨fun H y hy => ?_, fun H v hv => H _ hv⟩
  simpa using H (fun i => e (y i)) (by simpa using hy)

end Fields

variable {X : Fields} {D : D7} (s : Seam D X)

theorem sd_lat (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (h : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  refine (sd_iff D _).2 ⟨trL_fg s.iE h.1.fg, trL_span s.iE h.1.span_eq_top, fun y => ?_⟩
  have key : ∀ x : Fin n → D.host.E, IntE D (hE D y x) ↔
      hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) ∈ (1 : Submodule (𝓞 X.E) X.E) := by
    intro x
    have e1 : hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) = s.iE.symm (hE D y x) := by
      apply s.iE.injective
      change s.iE (∑ i, star (s.iE.symm (x i)) * s.iE.symm (y i)) = _
      simp only [map_sum, map_mul, hs.2, RingEquiv.apply_symm_apply, hE, mul_comm]
    rw [e1, ← mem_one_iff, Submodule.mem_one]
    rfl
  have hm : ∀ x, x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N
  simp only [key, hm]
  conv_lhs => rw [← h.2, Formalism.L2.Col.mem_dual]
  refine ⟨fun H x hx => H _ hx, fun H x hx => ?_⟩
  simpa using H (fun i => s.iE (x i)) (by simpa using hx)

theorem mem_AA_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (t : D.host.E) : t ∈ Iid D cc ↔ s.iE.symm t ∈ (ambOf s B χ cD).AA := by
  rw [← mem_trI]
  change _ ↔ t ∈ trI s.iE (Submodule.span _ _)
  rw [trI_span, Iid]
  congr! 2
  ext u
  constructor
  · rintro ⟨c, hc, a, ha, rfl⟩
    exact ⟨_, ⟨c, hc, a, ha, rfl⟩, s.iE.apply_symm_apply _⟩
  · rintro ⟨_, ⟨c, hc, a, ha, rfl⟩, rfl⟩
    exact ⟨c, hc, a, ha, s.iE.apply_symm_apply _⟩

theorem mem_RL_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (z : Matrix (Fin b) (Fin a) D.host.E) :
    z ∈ RL D cc (s.lat N) (s.lat N') ↔ (matT s.iE a b).symm z ∈ perO (ambOf s B χ cD).AA N N' := by
  rw [← mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), perO,
    span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), RL]
  congr! 2
  ext u
  constructor
  · rintro ⟨t, ht, A, hA, rfl⟩
    obtain ⟨x, rfl⟩ := (matT s.iE a b).surjective A
    refine ⟨_, ⟨_, (mem_AA_iff s B χ cD t).1 ht, x, (matT_carries s.iE N N' x).1 (mem_homL.1 hA), rfl⟩, ?_⟩
    rw [matT_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨r, hr, x, hx, rfl⟩, rfl⟩
    exact ⟨s.iE r, (mem_AA_iff s B χ cD _).2 (by simpa using hr), _,
      mem_homL.2 ((matT_carries s.iE N N' x).2 hx), matT_smul _ _ _⟩

theorem seam_lattices : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  intro X D s cc δ B χ cD hs
  refine ⟨fun n N h => sd_lat s hs h, fun a b N N' z => ?_⟩
  have hpt : ∀ (x : HomE X.E a b) (τ : X.Tau), embH (X.embC s.σ₀) δ x τ =
      StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matT s.iE a b x) (s.iT τ) := by
    intro x τ
    funext i j
    rw [pt_apply, matT_apply, ← hs.1]
    rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := pt_mem_La (δ := δ) ((mem_RL_iff s B χ cD N N' (matT s.iE a b x)).2 (by simpa using hx)) 1
    rw [one_smul] at h1
    convert h1 using 1
    funext τ
    exact (hpt x _).trans (by rw [Equiv.apply_symm_apply])
  · intro h
    obtain ⟨w, hw, e⟩ := La_sub h
    refine ⟨_, (mem_RL_iff s B χ cD N N' w).1 hw, funext fun τ => (hpt _ τ).trans ?_⟩
    rw [AddEquiv.apply_symm_apply, ← e]
    exact congrArg z (s.iT.symm_apply_apply τ)

end GlobalTheory.PeriodTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
section
noncomputable section

namespace GlobalTheory.ClassDuty

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

theorem exists_large (eps A : ℝ) (he : 0 < eps) (hA : 0 < A) :
    ∃ x0 : ℝ, ∀ x ≥ x0, A * (x ^ (eps / 5) * Real.log x ^ 2) < x ^ (eps / 3) ∧ 2 ≤ x ^ (eps / 16) ∧ 44 ^ 3 ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 2 * eps / 15) (by positivity)).bound
    (c := 1 / (2 * A)) (by positivity)
  have h' := (tendsto_rpow_atTop (y := eps / 16) (by positivity)).eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp ((h.and h').and (Filter.eventually_ge_atTop ((44 : ℝ) ^ 3)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨h1, h3⟩, h2⟩ := hx0 x hx
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  refine ⟨?_, h3, h2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h1
  have e : x ^ (eps / 3) = x ^ (eps / 5) * x ^ (2 * eps / 15) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < x ^ (2 * eps / 15) := Real.rpow_pos_of_pos hx0 _
  have h4 : A * Real.log x ^ 2 ≤ x ^ (2 * eps / 15) / 2 := by
    calc A * Real.log x ^ 2 ≤ A * (1 / (2 * A) * x ^ (2 * eps / 15)) := by gcongr
      _ = _ := by field_simp
  rw [e]
  nlinarith

theorem poly_lt {x w y : ℝ} (hx : 44 ^ 3 ≤ x) (hw : Real.log x ≤ w) (hy : 500 * w < y) :
    8 * x ^ (406 : ℝ) < Real.exp y := by
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  have hx1 : 1 ≤ x := by linarith [show (1 : ℝ) < 44 ^ 3 by norm_num]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  calc 8 * x ^ (406 : ℝ) ≤ x * x ^ (406 : ℝ) := by
        gcongr; linarith [show (8 : ℝ) < 44 ^ 3 by norm_num]
    _ = x ^ (407 : ℝ) := by rw [show (407 : ℝ) = 1 + 406 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    _ = Real.exp (Real.log x * 407) := Real.rpow_def_of_pos hx0 _
    _ < Real.exp y := Real.exp_lt_exp.2 (by linarith)

set_option maxHeartbeats 1000000 in

theorem windowsAt_of (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (hC : Std C) :
    ∃ x0 : ℝ, ∀ (cD ch : ℝ) (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → ParameterChoice' D L →
      WindowsAt L C.P.CY ∧ L.sc.X' ≤ lJ L := by
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hY : 1 ≤ C.P.CY := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x1, h1⟩ := exists_large eps (500 + 2 * C.P.Cpde + 2 * C.P.CY) he (by linarith)
  obtain ⟨x2, h2⟩ := rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := hostBounds eps C.P.Cpde he he' h8
  refine ⟨max x1 (max x2 x3), fun cD ch D L hs hx h P => ?_⟩
  obtain ⟨hA, h16, h44⟩ := h1 _ ((le_max_left _ _).trans hx)
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, -, -, -, -, -, ht, hN, hm1, hm2⟩ :=
    h2 _ _ hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) h.ranks
  obtain ⟨-, hq, -, hd, hcond, -, -, -, hp, hp'⟩ :=
    h3 _ _ _ hs (((le_max_right _ _).trans (le_max_right _ _)).trans hx) h.ranks h.host
  obtain ⟨⟨hn1, hn2⟩, ⟨hm1', hm2'⟩, ⟨hk1, hk2⟩, -⟩ := h.ranks
  have hg := h.host.2.2.2.2.1
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  subst hs
  clear h1 h2 h3 hx
  set s := L.sc with hs
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx1.le h
  have hlog : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9, show (3 : ℝ) < 44 ^ 3 by norm_num]
  set w := s.x ^ (s.eps / 5) * Real.log s.x ^ 2 with hw
  have h5 : 1 ≤ s.x ^ (s.eps / 5) := one (by linarith)
  have hl2 : Real.log s.x ≤ Real.log s.x ^ 2 := le_self_pow₀ hlog two_ne_zero
  have hlw : Real.log s.x ≤ w := hl2.trans (le_mul_of_one_le_left (sq_nonneg _) h5)
  have h5w : s.x ^ (s.eps / 5) ≤ w := le_mul_of_one_le_right (by linarith) (hlog.trans hl2)
  have hw1 : 1 ≤ w := hlog.trans hlw
  set u := s.x ^ (s.eps / 3) with hu
  have hA1 : 500 * w < u := (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA2 : 2 * C.P.Cpde * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA3 : 2 * C.P.CY * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hcond' : Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤ 2 * w := by rw [hw, ← mul_assoc]; exact hcond
  have hpw : Real.log D.host.pde < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp
  have hpw' : Real.log D.host.pde' < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp'
  have hX : s.X' = Real.exp u := rfl
  have hpoly : 8 * s.x ^ (406 : ℝ) < s.X' := poly_lt h44 hlw hA1
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by linarith)
  have hu2 : 2 * u ≤ s.L := by
    have : s.L = s.x ^ (2 * s.eps / 3) * u := by
      rw [hu, ← Real.rpow_add hx0, Scale.L]; congr 1; ring
    rw [this]
    have := h16.trans (mono (b := 2 * s.eps / 3) (by linarith))
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hXb : s.X' * s.X' ≤ s.b := by
    rw [hX, ← Real.exp_add, Scale.b]; exact Real.exp_le_exp.2 (by linarith)
  have hXb' : s.X' ≤ s.b := (le_mul_of_one_le_left (by linarith) hX1).trans hXb
  have hb1 : 1 ≤ s.b := hX1.trans hXb'
  have hk5 : (D.R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.2 hkr).trans hr
  have hk0 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 1 ≤ D.R.k)
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn0 : (1 : ℝ) ≤ D.R.n := (one (by linarith)).trans hn1
  have hlt : ∀ p : ℕ, p.Prime → Real.log p < u → (p : ℝ) < s.X' := fun p hp h =>
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hp.pos)).1 h
  refine ⟨⟨⟨⟨hn1, hn2, ?_⟩, ⟨?_, ?_⟩, hk1, hk2⟩, ⟨?_, ?_, ?_, ?_, hn2, hk2⟩, ⟨((D.R.k : ℝ) * s.b) ^ 8, le_rfl, ?_, ?_, hg⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · have : s.x ^ (1 : ℝ) ≤ D.R.n := (mono (by linarith)).trans hn1
    rw [Real.rpow_one] at this
    have : (4 : ℝ) ≤ D.R.n := by linarith [show (4 : ℝ) < 44 ^ 3 by norm_num]
    exact_mod_cast this
  · rw [← Real.sqrt_eq_rpow]; exact hm1'
  · rw [← Real.sqrt_eq_rpow]; exact hm2'
  · exact (mono (by linarith)).trans hm1
  · have : s.x ^ (1 / 2 : ℝ) = s.x ^ (s.eps / 16) * s.x ^ (1 / 2 - s.eps / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]
    exact hm2.trans (mul_le_mul_of_nonneg_right h16 (by positivity))
  · have h1 : s.x ^ (1 / 3 : ℝ) ≤ D.R.m := (mono (by linarith)).trans hm1
    have h2 : (44 : ℝ) ≤ s.x ^ (1 / 3 : ℝ) := by
      calc (44 : ℝ) = ((44 : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h44 (by norm_num)
    exact_mod_cast h2.trans h1
  · linarith
  · have e : (((D.R.k : ℝ) * s.b) ^ 8) ^ (1 / 4 : ℝ) = ((D.R.k : ℝ) * s.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]; norm_num
    have c0 : (0 : ℝ) < (LevelStarExponents.condE D : ℝ) := by
      have := hqp.pos; have := hdp.pos; have := D.host.QS_pos
      unfold LevelStarExponents.condE; push_cast; positivity
    have c1 : (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b := by
      rw [Real.rpow_def_of_pos c0]
      refine le_trans (Real.exp_le_exp.2 ?_) hXb'
      have : Real.log (LevelStarExponents.condE D : ℝ) ≤ 2 * w := by
        unfold LevelStarExponents.condE; push_cast; exact hcond'
      have := mul_le_mul_of_nonneg_right this (show 0 ≤ C.P.CY by linarith)
      linarith only [this, hA3]
    have c2 : (D.R.r : ℝ) ^ 4 ≤ s.b := by
      calc (D.R.r : ℝ) ^ 4 ≤ (s.x ^ (5 : ℝ)) ^ 4 := by gcongr
        _ = s.x ^ (20 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ s.x ^ (406 : ℝ) := mono (by norm_num)
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    rw [e]
    calc (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b * s.b := by gcongr
      _ = (1 * s.b) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · have c2 : 2 * (D.R.k : ℝ) ^ 8 ≤ s.b := by
      calc 2 * (D.R.k : ℝ) ^ 8 ≤ 2 * (s.x ^ (5 : ℝ)) ^ 8 := by gcongr
        _ = 2 * s.x ^ (40 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ 2 * s.x ^ (406 : ℝ) := by linarith [mono (show (40 : ℝ) ≤ 406 by norm_num)]
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    calc 2 * ((D.R.k : ℝ) * s.b) ^ 8 = 2 * (D.R.k : ℝ) ^ 8 * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := by gcongr
      _ = s.b ^ 9 := by ring
  · exact hlt _ hqp (by linarith)
  · exact hlt _ hdp (by linarith)
  · exact hlt _ D.host.pde_prime hpw
  · exact hlt _ D.host.pde'_prime hpw'
  · have hb0 : 0 < s.b := by linarith
    have e : s.X'' D.R.n = s.x * D.R.n * s.X' := by
      unfold Scale.X'' Scale.w'' Scale.b' Scale.a
      field_simp
    rw [e]
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hx1.le hn0)
  · have c1 := (rank_mul_le hx0 (Nat.cast_nonneg _) hf hN).trans (mono (b := 406) (by norm_num))
    linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
  · have hw'' : s.w'' D.R.n ≤ s.b := by
      have e : s.w'' D.R.n = s.b / (D.R.n * s.X') := by
        unfold Scale.w'' Scale.b' Scale.a
        field_simp
      rw [e]
      exact div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hn0 hX1)
    have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have hS : L.Sc ≤ s.b := ((le_mul_of_one_le_left L.Sc_pos.le hk0).trans P.kS_le).trans hw''
    have hE : L.etaSz ≤ s.b :=
      ((le_mul_of_one_le_left L.etaSz_pos.le (one_le_mul_of_one_le_of_one_le hm0 (by linarith))).trans P.mteta).trans hw''
    have hh : 3 * hWidth L ≤ 15 * s.b := by
      have := P.t_le_eta
      unfold hWidth; linarith
    have hh0 : 0 < 3 * hWidth L := by
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    have hlg : Real.log (3 * hWidth L) ≤ 4 * s.L := by
      have c1 := Real.log_le_log hh0 hh
      rw [Real.log_mul (x := 15) (by norm_num) (by linarith), Scale.b, Real.log_exp] at c1
      have c2 : Real.log 15 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num), show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        have := Real.exp_one_gt_d9
        have h7 : 7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith only [this]
        nlinarith only [this, h7]
      linarith
    have hmt : (D.R.m : ℝ) + D.R.t ≤ 2 * s.x ^ (401 : ℝ) := by
      have := mono (show (1 : ℝ) ≤ 401 by norm_num)
      rw [Real.rpow_one] at this
      linarith
    have e : s.x ^ (406 : ℝ) = s.x ^ (5 : ℝ) * s.x ^ (401 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    unfold lJ
    rw [le_div_iff₀ (lJ_den_pos L)]
    have hl0 : 0 ≤ Real.log (3 * hWidth L) := by
      apply Real.log_nonneg
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    calc s.X' * ((D.R.k : ℝ) * ((D.R.m : ℝ) + D.R.t) * Real.log (3 * hWidth L))
        ≤ s.X' * (s.x ^ (5 : ℝ) * (2 * s.x ^ (401 : ℝ)) * (4 * s.L)) := by gcongr
      _ = s.X' * (8 * s.x ^ (406 : ℝ)) * s.L := by rw [e]; ring
      _ ≤ s.X' * s.X' * s.L := by gcongr
      _ ≤ (1 * s.b) * s.L := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hXb (by linarith)
      _ ≤ (D.R.m : ℝ) * s.b * s.L := by gcongr

end GlobalTheory.ClassDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.AAUnitAway

theorem natCast_notMem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem exists_den (D : D7) (Q : Ideal (𝓞 D.host.E)) [hQ : Q.IsPrime] {l : ℕ} (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hlQ : (l : 𝓞 D.host.E) ∈ Q) :
    ∃ z : 𝓞 D.host.E, z ∉ Q ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * (z : D.host.E) := by
  have hnot : ¬ D.host.𝔟 ≤ Q := by
    intro hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hle).mul_right _
    exact natCast_notMem hQ.ne_top hlQ (Nat.Coprime.mul_left
      ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_QS D.host hl h2)).symm
      ((Nat.coprime_primes D.host.hyp.1 hl).2 hq.symm)) (D.host.der.diffSupport Q hQ hd)
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem localization_le_of_le_localization₂ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {I J : Submodule (𝓞 E) E}
    (h : I ≤ localization₂ P.asIdeal J) : localization₂ P.asIdeal I ≤ localization₂ P.asIdeal J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP P I x).1 hx
  obtain ⟨t, ht, hx⟩ := (mem_locP P J _).1 (h hx)
  refine (mem_locP P J x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases P.isPrime.mem_or_mem hm with h | h
  exacts [ht h, hs h]

theorem locP_AA (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ) (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hP : (l : 𝓞 X.E) ∈ P.asIdeal) (hc : Nat.Coprime (Ideal.absNorm cc) l) :
    localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  haveI := P.isPrime
  refine le_antisymm (localization_le_of_le_localization₂ P ?_) (localization_le_of_le_localization₂ P ?_)
  · obtain ⟨z, hz, hden⟩ := exists_den D (P.asIdeal.comap j) hl h2 hq (by rw [Ideal.mem_comap, map_natCast]; exact hP)
    refine Submodule.span_le.2 ?_
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine (mem_locP P _ _).2 ⟨j z, hz, Submodule.mem_one.2 ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    rw [e, hw]
    ring
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    refine (mem_locP P _ _).2 ⟨(Ideal.absNorm cc : ℕ), natCast_notMem P.isPrime.ne_top hP hc, ?_⟩
    have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
      refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
      simp
    convert Submodule.smul_mem _ y h1 using 1
    simp [Algebra.smul_def, mul_comm]

theorem sq_ne_neg {X : Fields} (hX : X.Ok) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f) (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p)
    (a : X.E) : a ^ 2 ≠ -(p : X.E) := by
  intro ha
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    exact (isIntegral_algebraMap (R := ℤ) (x := (p : ℤ)) |>.neg) |> fun h => by simpa using h
  obtain ⟨b, hba⟩ : ∃ b : 𝓞 X.E, algebraMap (𝓞 X.E) X.E b = a := ⟨⟨a, hint⟩, rfl⟩
  have hb : b ^ 2 = -(p : 𝓞 X.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hba, ha, map_neg, map_natCast]
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  have haP : b ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem 2 (hb ▸ P.asIdeal.neg_mem hpP)
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP ?_
  have := Ideal.pow_mem_pow haP 2
  rwa [hb, neg_mem_iff] at this

theorem notMem_small {X : Fields} (hX : X.Ok) (D : D7) (s : Seam D X) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime)
    (hn : π * X.conjO π = (p : 𝓞 X.E)) (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f)
    (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p) : p ∉ D.host.small := by
  intro hs
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  exact (UpperTheory.Ram.not_dvd_QS_of_notMem_sq D.host.toHostAx D.host.QS_exact X.E s.iE P p hp hpP
    (GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP)).1
    (Nat.dvd_of_mem_primeFactors hs)

theorem primes_ne (Z : Dat) (D : D7) (s : Seam D Z.X) (hZ : Z.Ok) :
    (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q := by
  have ha : (s.iE.symm (D.host.sqq)) ^ 2 = -(D.host.q : Z.X.E) := by
    rw [← map_pow, D.host.sqq_sq, map_neg, map_natCast]
  have hcc : ∀ x, Z.X.conjO (Z.X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : Z.X.E))
  have hPr := hZ.primes
  refine ⟨fun u => ⟨fun h => ?_, fun h => ?_⟩, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact notMem_small hZ.fields D s _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) h
  · exact sq_ne_neg hZ.fields _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) _ (h ▸ ha)
  · exact notMem_small hZ.fields D s (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) h
  · exact sq_ne_neg hZ.fields (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) _ (h ▸ ha)

theorem locP_AA_and_primes_ne : (∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ), l.Prime → l ∉ D.host.small → l ≠ D.host.q → (l : 𝓞 X.E) ∈ P.asIdeal → Nat.Coprime (Ideal.absNorm cc) l → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) ∧ ∀ (Z : Dat) (D : D7) (s : Seam D Z.X), Z.Ok → (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q :=
  ⟨locP_AA, primes_ne⟩

end GlobalTheory.AAUnitAway
end

