import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0100
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowsOfExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTwoLargeNormOnePrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem excluded_count_lt {Y r : ℝ} (hY : 1 ≤ Y) (hr : 1 ≤ r) (h : 20 * r ^ 3 < Y ^ ((3 : ℝ) / 20)) :
    (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < Y ^ ((9 : ℝ) / 10) := by
  have hP : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY (by norm_num)
  have hs : Y ^ ((9 : ℝ) / 10) = Y ^ ((3 : ℝ) / 20) * Y ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rw [hs]
  generalize Y ^ ((3 : ℝ) / 4) = P at hP ⊢
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h1 : 1 ≤ r ^ 2 * P := one_le_mul_of_one_le_of_one_le hr2 hP
  have h2 : r ^ 2 ≤ r ^ 2 * P := le_mul_of_one_le_right (by positivity) hP
  have h3 : 1 + 2 * r ^ 2 * (P + 1) ≤ 5 * (r ^ 2 * P) := by nlinarith
  calc (3 * r + 1) * (1 + 2 * r ^ 2 * (P + 1)) ≤ (4 * r) * (5 * (r ^ 2 * P)) :=
        mul_le_mul (by linarith) h3 (by positivity) (by positivity)
    _ = 20 * r ^ 3 * P := by ring
    _ < _ := mul_lt_mul_of_pos_right h (by linarith)

theorem exists_pair_disjoint_exceptional {Y : ℝ} {r : ℕ} (hY : 2 ≤ Y) (hr : 1 ≤ r)
    (h : 20 * (r : ℝ) ^ 3 < Y ^ ((3 : ℝ) / 20)) (G : Finset ℕ) (hG : ∀ g ∈ G, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : Y ^ ((9 : ℝ) / 10) ≤ G.card) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ Disjoint (Formalism.CyclotomicNorms.BB r a) (Formalism.CyclotomicNorms.BB r b) := by
  have hpos : 0 < Y ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hne : G.Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos.trans_le hc)
  obtain ⟨a, ha⟩ := hne
  have hex : ∃ b ∈ G, ¬ (Formalism.CyclotomicNorms.BB r b ∩ Formalism.CyclotomicNorms.BB r a).Nonempty := by
    by_contra hcon
    push Not at hcon
    have h1 := GlobalTheory.choice_count Y r a hY hr (hG a ha).1 (hG a ha).2 G
      (fun g hg => ⟨(hG g hg).1, (hG g hg).2, hcon g hg⟩)
    have h2 := excluded_count_lt (Y := Y) (r := r) (by linarith) (by exact_mod_cast hr) h
    linarith
  obtain ⟨b, hb, hab⟩ := hex
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · rintro rfl
    exact hab ⟨a, Or.inl rfl, Or.inl rfl⟩
  · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact Set.not_nonempty_iff_eq_empty.1 hab

theorem two_type_primes : NormPrimes → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → ModRow s N d → ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) := by
  classical
  intro hN eps he0 he1
  obtain ⟨x1, h1⟩ := hN eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 16 1 he0 one_pos
  obtain ⟨x3, h3⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max (max x1 x2) (max x3 21), fun s R q d hs hx hR hq => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hc := h1 s R q d hs hx1 hR hq
  have hb := (h2 s hs hx2).2.2.1
  obtain ⟨-, -, hr5, hkr, -⟩ := h3 s R hs hx3 hR
  have hmk := R.m_add_three_le_k
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hx0 : 0 < s.x := by linarith
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  rw [Real.rpow_one, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hb
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hr5
  have hb1 : s.x ^ 16 ≤ s.b := (le_mul_of_one_le_right (by positivity) hX).trans hb
  have hx15 : 1 ≤ s.x ^ 15 := one_le_pow₀ (by linarith)
  have hx16 : 21 * s.x ^ 15 ≤ s.x ^ 16 := by
    rw [pow_succ s.x 15, mul_comm]; exact mul_le_mul_of_nonneg_left hx4 (by linarith)
  have hb2 : 2 ≤ s.b := by linarith
  have hkb : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk1
  have hkb1 : 1 ≤ (R.k : ℝ) * s.b := by linarith
  have hY : 2 ≤ ((R.k : ℝ) * s.b) ^ 8 :=
    (hb2.trans hkb).trans (le_self_pow₀ hkb1 (by norm_num))
  have hr3 : (R.r : ℝ) ^ 3 ≤ s.x ^ 15 := by
    calc (R.r : ℝ) ^ 3 ≤ (s.x ^ 5) ^ 3 := pow_le_pow_left₀ (by positivity) hr5 3
      _ = _ := by ring
  have hZ : (R.k : ℝ) * s.b ≤ (((R.k : ℝ) * s.b) ^ 8) ^ ((3 : ℝ) / 20) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.self_le_rpow_of_one_le hkb1 (by norm_num)
  obtain ⟨a, ha, b, hb', hab, hd⟩ := exists_pair_disjoint_exceptional (r := R.r) hY (by omega)
    (by linarith) _ (fun g hg => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at hg
      exact ⟨hg.2.2.1, hg.1⟩) hc
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at ha hb'
  refine ⟨![a, b], ?_, hab, hd⟩
  intro i
  fin_cases i
  · exact ⟨ha.2.1, ha.2.2.1, ha.1, ha.2.2.2⟩
  · exact ⟨hb'.2.1, hb'.2.2.1, hb'.1, hb'.2.2.2⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m := by
    have : D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m := by
      unfold Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m := by
    have e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ) := by
      rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)
  have hth : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : szTh L ≤ 1 := by unfold szTh; rw [hε]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hxone this
  obtain ⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩ := nodeGap_poly hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m))
    (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hth hth hH
  refine ⟨?_, a2, a3, a5, a6, a7, a9⟩
  have hb : 0 < L.sc.b := by unfold Scale.b; positivity
  refine le_trans (le_of_eq ?_) a1
  unfold szlStar
  rw [div_div_eq_mul_div]
  field_simp

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
open GlobalTheory.IdealTransport GlobalTheory.ThetaLatImage
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SeamTransport

section Lat

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def matE (a b : ℕ) : HomE X.E a b ≃+ Matrix (Fin b) (Fin a) D.host.E :=
  (LinearMap.toMatrix' (R := X.E) (m := Fin b) (n := Fin a)).toAddEquiv.trans s.iE.toAddEquiv.mapMatrix

theorem matE_apply (x : HomE X.E a b) (i : Fin b) (j : Fin a) : matE s a b x i j = s.iE (x (Pi.single j 1) i) := by
  simp [matE, LinearMap.toMatrix'_apply]

theorem matE_smul (r : X.E) (x : HomE X.E a b) : matE s a b (r • x) = s.iE r • matE s a b x := by
  ext i j
  simp [matE_apply]

theorem matE_smul_int (r : 𝓞 X.E) (x : HomE X.E a b) :
    matE s a b (r • x) = RingOfIntegers.mapRingEquiv s.iE r • matE s a b x := by
  ext i j
  rw [matE_apply, Matrix.smul_apply, matE_apply, ← map_smul_int]
  rfl

theorem matE_mulVec (x : HomE X.E a b) (y : Sp X.E a) :
    (matE s a b x).mulVec (fun j => s.iE (y j)) = fun i => s.iE (x y i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matE_apply, LinearMap.toMatrix'_apply]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Fin n → D.host.E) :
    x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N x

theorem matE_mem_homL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') ↔ x ∈ homO N N' := by
  rw [mem_homL]
  constructor
  · intro H y hy
    have := H (fun j => s.iE (y j)) ((mem_lat s N _).2 (by simpa using hy))
    rw [matE_mulVec, mem_lat] at this
    simpa using this
  · intro H v hv
    have hv' : v = fun i => s.iE (s.iE.symm (v i)) := by simp
    rw [hv', matE_mulVec, mem_lat]
    simpa using H _ ((mem_lat s N _).1 hv)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem mem_Iid (r : X.E) : s.iE r ∈ GlobalTheory.InertSign.Iid D cc ↔ r ∈ (ambOf s B χ cD).AA := by
  have : GlobalTheory.InertSign.Iid D cc = trI s.iE (ambOf s B χ cD).AA := by
    refine Eq.trans ?_ (trI_span s.iE _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext t
    constructor
    · rintro ⟨c, hc, t, ht, rfl⟩
      exact ⟨_, ⟨c, hc, t, ht, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, t, ht, rfl⟩, rfl⟩
      exact ⟨c, hc, t, ht, by simp⟩
  rw [this, mem_trI, RingEquiv.symm_apply_apply]

theorem matE_mem_RL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') ↔ x ∈ perO (ambOf s B χ cD).AA N N' := by
  have : GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') =
      Submodule.span (𝓞 D.host.E) (matE s a b '' (perO (ambOf s B χ cD).AA N N' : Set (HomE X.E a b))) := by
    refine Eq.trans ?_ (span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s) _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext z
    constructor
    · rintro ⟨t, ht, A, hA, rfl⟩
      obtain ⟨t, rfl⟩ := s.iE.surjective t
      obtain ⟨A, rfl⟩ := (matE s a b).surjective A
      exact ⟨_, ⟨t, (mem_Iid s B χ cD t).1 ht, A, (matE_mem_homL s N N' A).1 hA, rfl⟩, matE_smul s t A⟩
    · rintro ⟨_, ⟨t, ht, A, hA, rfl⟩, rfl⟩
      exact ⟨_, (mem_Iid s B χ cD t).2 ht, _, (matE_mem_homL s N N' A).2 hA, matE_smul s t A⟩
  rw [this, mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s), AddEquiv.symm_apply_apply]

theorem pt_matE (hs : s.Ok) (x : HomE X.E a b) (τ : X.Tau) :
    StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b x) (s.iT τ) = embH (X.embC s.σ₀) δ x τ := by
  funext i j
  rw [pt_apply, matE_apply, ← hs.1]
  rfl

theorem mem_La (hs : s.Ok) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b) :
    z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔
      (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N' := by
  constructor
  · intro hz
    obtain ⟨A, hA, rfl⟩ := La_sub hz
    obtain ⟨A, rfl⟩ := (matE s a b).surjective A
    exact ⟨A, (matE_mem_RL s B χ cD N N' A).1 hA, funext fun τ => (pt_matE s hs A τ).symm⟩
  · rintro ⟨A, hA, e⟩
    have hz : z = StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b A) := by
      funext τ
      obtain ⟨τ, rfl⟩ := s.iT.surjective τ
      rw [pt_matE s hs, e]
    rw [hz]
    simpa using pt_mem_La (δ := δ) ((matE_mem_RL s B χ cD N N' A).2 hA) 1

theorem sd_lat (hs : s.Ok) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  obtain ⟨hl, hu⟩ := hN
  let f : Sp X.E n ≃+ (Fin n → D.host.E) := AddEquiv.piCongrRight fun _ : Fin n => s.iE.toAddEquiv
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 hl.fg
    refine Submodule.fg_def.2 ⟨f '' S, hS.image _, ?_⟩
    exact (span_image_span (RingOfIntegers.mapRingEquiv s.iE) f
      (fun r m => funext fun i => map_smul_int s.iE r (m i)) S).symm
  · rw [eq_top_iff]
    intro v _
    have h1 := span_image_span s.iE f (fun r m => funext fun i => map_mul s.iE r (m i)) (N : Set (Sp X.E n))
    have h2 : v ∈ Submodule.span D.host.E (f '' (N : Set (Sp X.E n))) := by
      rw [← h1, hl.span_eq_top]
      exact Submodule.subset_span ⟨f.symm v, trivial, by simp⟩
    exact Submodule.span_mono (fun w hw => Submodule.subset_span hw) h2
  · have key : ∀ x y : Sp X.E n, GlobalTheory.InertSign.IntE D (GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i))) ↔
        hStd X.E n x y ∈ (1 : Submodule (𝓞 X.E) X.E) := by
      intro x y
      have e : GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i)) = s.iE (hStd X.E n x y) := by
        change _ = s.iE (∑ i, star (x i) * y i)
        simp only [GlobalTheory.InertSign.hE, map_sum, map_mul, hs.2, mul_comm]
      rw [e, ← s.iE.symm_apply_apply (hStd X.E n x y), ← mem_one_iff, s.iE.symm_apply_apply, Submodule.mem_one]
      rfl
    intro y
    have hy : y = fun i => s.iE (s.iE.symm (y i)) := by simp
    rw [mem_lat, ← hu, mem_dual, hu]
    constructor
    · intro H x hx
      have hx' : x = fun i => s.iE (s.iE.symm (x i)) := by simp
      rw [hy, hx', key]
      exact H _ ((mem_lat s N x).1 hx)
    · intro H x hx
      rw [← key, ← hy]
      exact H _ ((mem_lat s N _).2 (by simpa using hx))

theorem form_eq (z w : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ)) := by
  change (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℂ) =
    (((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, z (s.iT τ) i j * (starRingEnd ℂ) (w (s.iT τ) i j)
  rw [Equiv.sum_comp s.iT fun τ => ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j), Complex.ofReal_inv, div_eq_inv_mul]

end Lat

section Taylor

variable {ι κ : Type} [Fintype ι] [Fintype κ] {a b : ℕ}

theorem deriv_transport (e : ι ≃ κ) (G : VCx κ a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 (fun z : VCx ι a b => G fun τ => z (e.symm τ)) m = derivAt0 G (m.mapDomain fun v => (e v.1, v.2)) := by
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  let L : VCx ι a b →L[ℂ] VCx κ a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hL : ∀ v : DVar ι a b, L (coordX v) = coordX (e v.1, v.2) := by
    intro v
    funext τ i j
    change coordX v (e.symm τ) i j = _
    unfold coordX
    congr 1
    exact propext (and_congr_left' e.symm_apply_eq)
  have h1 : (fun z : VCx ι a b => G fun τ => z (e.symm τ)) = G ∘ L := rfl
  unfold derivAt0
  rw [h1, L.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hc : (Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).card = (Finsupp.toMultiset m).card := by
    rw [← Finsupp.toMultiset_map, Multiset.card_map]
  have p : (((Finsupp.toMultiset m).toList.map fun v => (e v.1, v.2)).map coordX).Perm
      ((Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p (Finsupp.toMultiset m).card (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx κ a b) (w : Fin n' → VCx κ a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp [hL]
  · simp

end Taylor

theorem taylor_eq (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) (m : TaylorLogMetric.Mono D a b) :
    derivAt0 G m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G m := by
  have h : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold TaylorLogMetric.taylor
  rw [mul_div_cancel₀ _ h]
  unfold derivAt0
  congr 1

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  intro D X s cc δ B χ cD a b hs
  refine ⟨mem_La s B χ cD hs, fun N N' ha hb hN hN' => ⟨ha, hb, sd_lat s hs N hN, sd_lat s hs N' hN'⟩, form_eq s B χ cD,
    fun G hG m => ?_⟩
  rw [deriv_transport s.iT G hG m, taylor_eq, Finsupp.prod_mapDomain_index_inj]
  intro v w h
  exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2

end GlobalTheory.SeamTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeyl
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply]

theorem hw_mem_of_lt : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  intro p hp k _ _ N ν hν hal M M' hM hM' hlt hle
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p := by
    intro h
    refine ⟨(hal h).1, ?_, (hal h).2⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq p hp k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWHlatIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem mem_locW_hlat_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ emb Pl pw hv n S lam h hS w x
  unfold locW
  simp only [vl_mem_span_intW_iff Pl pw hv]
  unfold Formalism.HermitianLatticesTheory.localization₂
  constructor
  · rintro ⟨s, hs, hsx⟩ c
    exact ⟨s, hs, hsx c⟩
  · classical
    intro hx
    choose t ht htx using hx
    have : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b)) := hS.fin_orb
    let _ : Fintype S.Cl := Fintype.ofFinite _
    refine ⟨∏ c, t c, Submonoid.prod_mem _ fun c _ => ht c, fun c => ?_⟩
    have hc := (delAtr emb lam (S.Lsh c.1 (S.rep c))).smul_mem (∏ d ∈ Finset.univ.erase c, t d) (htx c)
    rw [← mul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at hc
    exact hc

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParametersWindowsOfExplicitParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windows_of_explicitParameters : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C8 D.host → (∀ t, s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ 2 * s.b') → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → let η : ℝ := (D.R.m : ℝ) * (h0v s ch : ℝ); let S : ℝ := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ)); (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3) ∧ (∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + η + 1) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + s.b' / s.x + η) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + η) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → S ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * S) ∧ (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ S) ∧ (∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) ∧ 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ 10 * ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ + 20 ≤ D.host.Lw ∧ 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n := by
  first | exact @GlobalTheory.EX.windows_of_large_scale | exact GlobalTheory.EX.windows_of_large_scale | (intros; apply GlobalTheory.EX.windows_of_large_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.LatAll → B.QIntAll := by
  first | exact @GlobalTheory.ThetaMove.qIntAll_of_latAll | exact GlobalTheory.ThetaMove.qIntAll_of_latAll | (intros; apply GlobalTheory.ThetaMove.qIntAll_of_latAll <;> assumption)
end

