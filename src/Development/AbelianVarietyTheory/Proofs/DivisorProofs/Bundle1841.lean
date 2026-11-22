import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1808
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdeal
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.FixKey

theorem hatId_mul {D : D7} {I : Ideal (𝓞 D.host.E)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ hatId D I) :
    s * y ∈ hatId D I := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem zeroAt_zero (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem suppSplit_one (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

theorem suppInert_one (D : D7) (N : ℕ) : SuppInert D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

theorem wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem TT_smul {D : D7} {T : Tor D} {N N' : ℕ} (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') :
    c • F ∈ TT D T N N' := by
  obtain ⟨hd, m, hm, h⟩ := hF
  exact ⟨hd.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

theorem weylTranslate_add_of_mem_baseLattice {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (hne : e0 ≠ 0) {x y : VC D a d}
    (hx : x ∈ La0 D (tor0 D ⊤ δ) a d) (hy : y ∈ La0 D (tor0 D ⊤ δ) a d) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (Wd D (tor0 D ⊤ δ) y F) = Wd D (tor0 D ⊤ δ) (x + y) F := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) x y
  have h2 := hφ e0
  rw [VacMove.wd_fix h1 hc k0 he hy, VacMove.wd_fix h1 hc k0 he hx,
    VacMove.wd_fix h1 hc k0 he (add_mem hx hy)] at h2
  have h3 : φ = 1 := by
    by_contra hne'
    apply hne
    have : (φ - 1) • e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  rw [hφ, h3, one_smul]

theorem unitBlock_int (D : D7) (o a d : ℕ) : ∀ i j, ∃ b : 𝓞 D.host.E, unitBlock D o a d i j = (b : D.host.E) := by
  intro i j
  by_cases h : i.1 = o + j.1
  · exact ⟨1, by simp [unitBlock, h]⟩
  · exact ⟨0, by simp [unitBlock, h]⟩

theorem om_cosetV_of_congOne : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ o : ℕ, o + a ≤ d → ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 (cosetV D δ 𝔪 o a d e0) = cosetV D δ 𝔪 o a d e0 := by
  intro D δ t0 hc a d e0 hv W 𝔪 h𝔪 hcop hch o ho k hk hck
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he

  have hk0 : W.Om k 1 e0 = e0 := by
    obtain ⟨ks, ki, x, hkk, hks, hki, hss, hsi, hxq, hxd, hxu, η, hη, hx1⟩ := GlobalTheory.T.exists_split_inert_factorization_unitaryLatticeStabilizer D k hk
    have hi : W.Om ki 1 e0 = e0 :=
      W.inert ki 1 ((mem_intG ki).1 hki) ((mem_intG 1).1 (one_mem _)) hsi (suppInert_one D d)
    have hs : W.Om ks 1 e0 = e0 := by
      have hm : Moves D (ks : GL (Fin a) (AE D)) (stdL D a) := by
        simpa using VacMove.moves_mul_int hks (VacMove.moves_one D a)
      have hx : W.chV'.f x = 1 := hch x hxu (by rw [hx1]; exact hatId_mul hη (GlobalTheory.T.unitary_congruent_one_det_sub_one_mem_ideal_mul_conj D 𝔪 hcop k hk hck))
      rw [W.split ks 1 x 1 (stdL D a) (stdL D d) hss (suppSplit_one D d)
        (fun q hq hi => ⟨hxq q hq hi, by simpa using zeroAt_zero D q⟩) hxd (by simp) hm (VacMove.moves_one D d)]
      simp only [hx, map_one, one_zpow, mul_one, Units.val_one, one_mul]
      exact VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) a d) he
    have := W.mul ks ki 1 1 e0 hT
    rw [mul_one, ← hkk] at this
    rw [this, hi, hs]

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hJT : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈
      TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact TT_smul _ (W.maps 1 g' e0 hT)
  have hkJ : W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one, hk0] at e2
    rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2]

  have hx₀ := pt_unitBlock_mem (D := D) δ o a d
  obtain ⟨m, hm, hlift⟩ := W.lift k 1 (unitBlock D o a d) _ hJT
  obtain ⟨w, hw𝔪, hclose⟩ := GlobalTheory.T.exists_ideal_matrix_approx_congruent_one_translate D 𝔪 h𝔪 k hk hck (unitBlock D o a d) (unitBlock_int D o a d) m hm
  have hw := GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  have hWJ := hlift _ hclose
  rw [hkJ, VacMove.pt_add, ← weylTranslate_add_of_mem_baseLattice hc he W.nz hx₀ hw.1, VacMove.wd_fix h1 hc hBk hJB hw.2] at hWJ
  unfold cosetV
  rw [W.smul _ _ _ _ (GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT), hWJ]

end GlobalTheory.FunObj.FixKey
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem per_mM {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {m : ℕ} {f : (κ → AF F) → ℂ}
    (h : Per F m f) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : Per F m (mM F l f) := by
  intro x z hz
  have hev : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have ha : arch F (x + z) = arch F x := by
    funext i
    obtain ⟨a, ha0, -, hza⟩ := hz i
    show evI F (x i + z i) = evI F (x i)
    rw [hev, hza, hmul, ha0, mul_zero, add_zero]
  unfold mM
  rw [ha, h x z hz]

theorem norm_word_rep {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) (N : ℕ) :
    ‖word F (List.replicate N (Sum.inr l)) f x‖ = |l (arch F x)| ^ N * ‖f x‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, word_cons]
    show ‖(l (arch F x) : ℂ) * word F (List.replicate N (Sum.inr l)) f x‖ = _
    rw [norm_mul, ih, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    ring

theorem om_bound_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨K, l, C0, hl, hpoly⟩ := GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow F (Fin n × Fin d) N
  obtain ⟨P, Cs, c, hsob⟩ := GlobalTheory.T.sobolev_bound_periodic_schwartz F (Fin n × Fin d) μ hμ
  obtain ⟨C1, k1, hfin⟩ := GlobalTheory.T.weilRep_finite_periodicity_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C2, k2, hL2⟩ := GlobalTheory.T.word_action_square_integrable_bound F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ (P + N)
  set A : ℝ := max (max Cs 0 * max C1 1 ^ c * max C2 0) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨max C0 0 * (K + 1) * A, k1 * c + k2, fun g h x => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  obtain ⟨m, hm0, hmC, hper⟩ := hfin g h

  have key : ∀ w : List (Op F (Fin n × Fin d)), w.length ≤ N → (∀ o ∈ w, ∃ l', o = Sum.inr l' ∧ ‖l'‖ ≤ 1) →
      ‖word F w (om (g, h) Φ) x‖ ≤ A * H ^ (k1 * c + k2) := by
    intro w hw hwo
    have hS : word F w (om (g, h) Φ) ∈ schA F (Fin n × Fin d) ∧ Per F m (word F w (om (g, h) Φ)) := by
      clear hw
      induction w with
      | nil => exact ⟨(hP.weil.isUSplitting).pres _ _ hΦ, hper⟩
      | cons o w ih =>
        obtain ⟨l', rfl, -⟩ := hwo o List.mem_cons_self
        obtain ⟨i1, i2⟩ := ih fun o' ho' => hwo o' (List.mem_cons_of_mem _ ho')
        exact ⟨GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr l') _ i1, per_mM i2 l'⟩
    have hH0 : 0 ≤ H := le_trans zero_le_one hH1
    have hb : 0 ≤ max C2 0 * H ^ k2 := mul_nonneg (le_max_right _ _) (pow_nonneg hH0 _)
    have hw' : ∀ v : List (Fin n × Fin d → mixedEmbedding.mixedSpace F), v.length ≤ P → (∀ u ∈ v, ‖u‖ ≤ 1) →
        ∫⁻ y, ‖wordD F v (word F w (om (g, h) Φ)) y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (max C2 0 * H ^ k2) := by
      intro v hv hv1
      have hlen : (v.map Sum.inl ++ w).length ≤ P + N := by
        rw [List.length_append, List.length_map]; omega
      have hsz : ∀ o ∈ v.map Sum.inl ++ w, size F o ≤ 1 := by
        intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ho
          exact hv1 u hu
        · obtain ⟨l', rfl, hl'⟩ := hwo o ho
          exact hl'
      have h3 := hL2 g h (v.map Sum.inl ++ w) hlen hsz
      rw [word_append] at h3
      exact h3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)))
    have h2 := hsob m hm0 _ hS.1 hS.2 (max C2 0 * H ^ k2) hb hw' x
    have hm' : (m : ℝ) ^ c ≤ (max C1 1 * H ^ k1) ^ c :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))) c
    have e1 : ‖word F w (om (g, h) Φ) x‖ ^ 2 ≤ A * H ^ (k1 * c + k2) := by
      refine h2.trans ?_
      calc Cs * (m : ℝ) ^ c * (max C2 0 * H ^ k2)
          ≤ max Cs 0 * (max C1 1 * H ^ k1) ^ c * (max C2 0 * H ^ k2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) hm' (by positivity) (le_max_right _ _)) hb
        _ = (max Cs 0 * max C1 1 ^ c * max C2 0) * H ^ (k1 * c + k2) := by
            rw [mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ A * H ^ (k1 * c + k2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)
    have hT : 1 ≤ A * H ^ (k1 * c + k2) := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hH1)
    nlinarith [norm_nonneg (word F w (om (g, h) Φ) x)]
  have hx := hpoly (arch F x)
  have k0 : ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := by
    simpa using key [] (by simp) (by simp)
  have kj : ∀ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := fun j => by
    have h4 := key (List.replicate N (Sum.inr (l j))) (by simp)
      (fun o ho => ⟨l j, List.eq_of_mem_replicate ho, hl j⟩)
    rwa [norm_word_rep] at h4
  show ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N ≤ _
  calc ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N
      ≤ ‖om (g, h) Φ x‖ * (max C0 0 * (1 + ∑ j, |l j (arch F x)| ^ N)) :=
        mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
          (norm_nonneg _)
    _ = max C0 0 * (‖om (g, h) Φ x‖ + ∑ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ max C0 0 * (A * H ^ (k1 * c + k2) + ∑ _j : Fin K, A * H ^ (k1 * c + k2)) :=
        mul_le_mul_of_nonneg_left (add_le_add k0 (Finset.sum_le_sum fun j _ => kj j)) (le_max_right _ _)
    _ = max C0 0 * (K + 1) * A * H ^ (k1 * c + k2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSkewIdealLatticeUnitVectorUnimodularEigenStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  first | exact @GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig | exact GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig | (intros; apply GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittChangeBasisUnitaryIso
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkChart

theorem exists_conj {Γ : Type} [Group Γ] (H K : Subgroup Γ) (t : Γ) (h : ∀ g, g ∈ H ↔ t⁻¹ * g * t ∈ K) :
    ∃ κ : H ≃* K, ∀ g, (κ g).1 = t⁻¹ * g.1 * t :=
  ⟨{ toFun := fun g => ⟨t⁻¹ * g.1 * t, (h _).1 g.2⟩
     invFun := fun k => ⟨t * k.1 * t⁻¹, (h _).2 (by simpa [mul_assoc] using k.2)⟩
     left_inv := fun g => Subtype.ext (by simp [mul_assoc])
     right_inv := fun g => Subtype.ext (by simp [mul_assoc])
     map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl⟩

theorem gram_iff {R : Type} [CommRing R] {k : ℕ} (g g' S S' C C' J : Matrix (Fin k) (Fin k) R)
    (h1 : S * S' = 1) (h2 : C * C' = 1) :
    gᵀ * J * g' = J ↔ (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * J * C := by
  have h3 : S'ᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e : (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * (gᵀ * J * g') * C := by
    calc _ = Sᵀ * (gᵀ * (S'ᵀ * Sᵀ) * J * (C * C') * g') * C := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.mul_one]
  rw [e]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have f : ∀ X : Matrix (Fin k) (Fin k) R, S'ᵀ * (Sᵀ * X * C) * C' = X := fun X => by
    calc _ = (S'ᵀ * Sᵀ) * X * (C * C') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.one_mul]
  rw [← f (gᵀ * J * g'), h, f]

theorem conj_iff {D : D7} {k : ℕ} (x W : Mx D k k) (hW : cj W = W) :
    xᵀ * W * cj x = W ↔ adj x * W * x = W := by
  constructor
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, cj_cj, hW, cj_transpose, ← adj_eq] at this
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, hW, adj_eq, cj_transpose, cj_cj] at this

theorem cj_Jst (D : D7) (n : ℕ) :
    cj (rat (StdUnn.Jst D n) : Mx D (n + n) (n + n)) = rat (StdUnn.Jst D n) := by
  rw [rat_Jst, cj, block_matrix_map]
  change StdUnn.blk4 (cj 0) (cj 1) (cj (-1)) (cj 0) = _
  rw [cj_neg, cj_zero, cj_one]

theorem mem_UG_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ (g.1 : Mx D k k)ᵀ * rat J * cj g.1 = rat J := by
  rw [← map_cAl, ← incM_eq]
  exact Iff.rfl

theorem mem_HR_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig J ↔ adj (g.1 : Mx D k k) * rat J * g.1 = rat J := Iff.rfl

theorem mat_iff {D : D7} {k : ℕ} (g S S' J W : Mx D k k) (h1 : S * S' = 1) (hG : Sᵀ * J * cj S = W) (hW : cj W = W) :
    gᵀ * J * cj g = J ↔ adj (S' * g * S) * W * (S' * g * S) = W := by
  have hc : cj S * cj S' = 1 := by rw [← cj_mul, h1, cj_one]
  rw [← conj_iff _ _ hW, cj_mul, cj_mul, ← hG]
  exact gram_iff g (cj g) S S' (cj S) (cj S') J h1 hc

theorem mem_iff {D : D7} {k : ℕ} (J W : Matrix (Fin k) (Fin k) D.host.E) (t : GL (Fin k) (AE D))
    (hG : (t.1 : Mx D k k)ᵀ * rat J * cj t.1 = rat W) (hW : cj (rat W : Mx D k k) = rat W) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ t⁻¹ * g * t ∈ HR (AF D.host.F) D.sp.cm.sig W := by
  rw [mem_UG_iff, mem_HR_iff, Units.val_mul, Units.val_mul]
  exact mat_iff g.1 t.1 (t⁻¹).1 _ _ t.mul_inv hG hW

theorem exists_isChartW : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  intro D n J₂ T hG
  have hW : (rat T.1 : Mx D (n + n) (n + n))ᵀ * rat J₂ * cj (rat T.1) = rat (StdUnn.Jst D n) := by
    rw [← hG, rat_mul, rat_mul, cj_rat]; rfl
  obtain ⟨κ, hκ⟩ := exists_conj _ _ _
    (mem_iff J₂ (StdUnn.Jst D n) ⟨rat T.1, rat (T⁻¹).1, rat_mul_inv T, rat_inv_mul T⟩ hW (cj_Jst D n))
  refine ⟨κ, fun g => ?_⟩
  exact congrArg Units.val (hκ g)

end GlobalTheory.SWLinkChart

end
end

