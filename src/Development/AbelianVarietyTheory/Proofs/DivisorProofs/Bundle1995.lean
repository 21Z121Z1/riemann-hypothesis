import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLevelCong

variable {D : D7} {T : Type}

theorem gridModulus_le_of_mem_chosenPlaces {L : LevCh D T} {sc : Consts} (G : GridData L sc) {PP : Pl D.host.E} (h : PP ∈ G.pl.W0) :
    G.modul ≤ PP.asIdeal := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  calc G.modul = ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u := rfl
    _ ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    _ ≤ _ := Ideal.pow_le_self (G.pl.depth_pos sc v).ne'

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem congLev_le_lev {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    congLev D.sp.cm D.sp.X'.gram L.ΛX G.modul ≤ lev D.sp.cm D.sp.X'.gram L.βX (L.datXt μ₀) := by
  intro x hx
  obtain ⟨c, hc⟩ := hL.βX
  rw [one_pow] at hc
  have hβ : IsFrame L.βX L.ΛX := hc.1
  have hS : x ∈ St L.βX := (GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ x hx.1 hS fun PP hP => ?_
  have hPg : PP ∈ L.Pg := by
    rcases hP with h | h
    · exact h
    · exfalso
      refine (hL.Q_ram μ₀ PP).2 (Or.inl h) ?_
      rw [hL.xi_base]
      exact fun _ _ => rfl
  have hle : G.modul ≤ PP.asIdeal := gridModulus_le_of_mem_chosenPlaces G (levelChainTypePlaces_subset_chosenPlaces G hL μ₀ hPg)
  refine GlobalTheory.LevRedTriv.redFn_eq_one_of_cols hβ PP x hS 1 ((Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top) fun j => ?_
  have hz := (hβ (L.βX.1 *ᵥ Pi.single j 1)).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h1 := hx.2.2 _ hz
  rw [map_one, Subring.coe_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) h1

end GlobalTheory.RowLevelCong

namespace GlobalTheory.ClassCount

open GlobalTheory.RowLevelCong

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in

theorem levRow_congLev_le : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε →
    x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is →
    ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1),
    congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤
      ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  refine ⟨0, fun CF _ ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ i => ?_⟩⟩
  have hL := hS.core.lev
  rcases i with ⟨_ | i, hi⟩
  · show congLev D.sp.cm (ch.G.V (.grid 0 D.R.m)).gram (ch.G.Λ (.grid 0 D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 0 (Nat.zero_le _)
    have e := GlobalTheory.FunObj.levRow_zero_eq_lev ch.W ch.S.toGridChoice hL A.μ0 (Nat.zero_le _)
    have key : ∀ (Y : LSp D) (K : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))), Y = ⟨D.sp.X', R.toLevCh.ΛX⟩ →
        HEq K (lev D.sp.cm D.sp.X'.gram R.toLevCh.βX (R.toLevCh.datXt A.μ0)) →
        congLev D.sp.cm Y.sp.gram Y.lat ch.G.modul ≤ K := by
      rintro _ K rfl e'
      obtain rfl := eq_of_heq e'
      exact congLev_le_lev ch.G hL
    exact (key (ch.G.node (.grid 0 D.R.m)) _ (colY_m _) e).trans inf_le_left
  · show congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi)
    have e := GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice A.μ0 i (Nat.le_of_lt_succ hi)
    calc congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul
        ≤ ch.G.levMax (.grid (i + 1) D.R.m) := congLev_mono le_top
      _ = ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi) ⊓ UA D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram := e.symm
      _ ≤ _ := inf_le_left

end GlobalTheory.ClassCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOne
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevScalar

open scoped Matrix

section Alg

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_eig_of_congr (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (M : ℕ) (hM : M ≠ 0) (A : Matrix (Fin r) (Fin r) E)
    (hA : ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = M • y) (τ : E →+* ℂ) (w : Fin r → ℂ) (hw : w ≠ 0) (lam : ℂ)
    (he : w ᵥ* A.map τ = lam • w) : IsIntegral ℤ ((lam - 1) / M) := by
  classical
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun v => w ⬝ᵥ (τ ∘ v)
      map_zero' := by simp [dotProduct]
      map_add' := fun a b => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ v, φ v = w ⬝ᵥ (τ ∘ v) := fun _ => rfl
  have hφA : ∀ v, φ (A *ᵥ v) = lam * φ v := by
    intro v
    have : (τ ∘ (A *ᵥ v)) = A.map τ *ᵥ (τ ∘ v) := by
      funext i; exact RingHom.map_mulVec τ A v i
    rw [hφ, hφ, this, Matrix.dotProduct_mulVec, he, smul_dotProduct, smul_eq_mul]
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) _
  let ψ : Λ →ₗ[ℤ] ℂ := (φ.comp Λ.subtype.toAddMonoidHom).toIntLinearMap
  have hψ : ∀ x : Λ, ψ x = φ x := fun _ => rfl
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine isIntegral_of_smul_mem_submodule (LinearMap.range ψ) ?_ ?_ _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := fun x hx => by
      have : ψ ⟨x, hx⟩ ∈ LinearMap.range ψ := ⟨_, rfl⟩
      rw [h0] at this
      exact this
    have h2 : ∀ x : Fin r → E, φ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span E (Λ : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact map_zero φ
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx =>
        have : (τ ∘ (a • x)) = τ a • (τ ∘ x) := by funext i; simp
        rw [hφ] at hx
        rw [hφ, this, dotProduct_smul, hx, smul_zero]
    apply hw
    funext i
    have := h2 (Pi.single i 1)
    have e : (τ ∘ (Pi.single i (1 : E) : Fin r → E)) = Pi.single i 1 := by
      funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hφ, e] at this
    simpa using this
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hA x hx
    refine ⟨⟨y, hy⟩, ?_⟩
    have := congrArg φ hxy
    rw [map_sub, hφA, map_nsmul, nsmul_eq_mul] at this
    rw [hψ, hψ, smul_eq_mul]
    field_simp
    linear_combination -this

theorem det_ne_zero_of_gram [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (u : Matrix (Fin r) (Fin r) ℂ) (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  have e : gram τ G u = uᵀ * (G.map τ * u.map (starRingEnd ℂ)) := by
    ext a b
    simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  intro h0
  have h1 : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  rw [← hu, e, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul] at h1
  exact hG ((map_eq_zero τ).1 h1.symm)

theorem eq_one_of_congr (ζ : E) (hζ : ∀ φ : E →+* ℂ, ‖φ ζ‖ = 1) (M : ℕ) (hM : 3 ≤ M)
    (hi : IsIntegral ℤ ((ζ - 1) / M)) : ζ = 1 := by
  by_contra hne
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h0 : (⟨(ζ - 1) / M, hi⟩ : 𝓞 E) ≠ 0 := fun h =>
    div_ne_zero (sub_ne_zero.2 hne) hM0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := NumberField.exists_conjugate_one_le_norm h0
  have h1 : 1 ≤ ‖φ ((ζ - 1) / M)‖ := hφ
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, le_div_iff₀ (by linarith), map_sub, map_one] at h1
  have h2 := norm_sub_le (φ ζ) 1
  rw [hζ, norm_one] at h2
  linarith

theorem norm_eq_one_of_herm [IsCMField E] (hr : 0 < r) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (ζ : E)
    (h : ∀ v w, herm G (ζ • v) (ζ • w) = herm G v w) (φ : E →+* ℂ) : ‖φ ζ‖ = 1 := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hs : ∀ v w, herm G (ζ • v) (ζ • w) = ζ * cc ζ * herm G v w := by
    intro v w
    simp only [herm, cc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hb : ∀ a b, herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
    intro a b
    simp [herm, cc, Pi.single_apply, apply_ite]
  have h1 : ζ * cc ζ = 1 := by
    by_contra hne
    apply hG
    have : G = 0 := by
      ext a b
      have := (hs (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
      rw [hb] at this
      exact (mul_left_eq_self₀.1 this).resolve_left hne
    rw [this, Matrix.det_zero]
  have h2 := congrArg (fun x => ‖φ x‖) h1
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
    Complex.norm_conj] at h2
  nlinarith [norm_nonneg (φ ζ)]

theorem exists_row_eig (hr : 0 < r) (A : Matrix (Fin r) (Fin r) ℂ) :
    ∃ (lam : ℂ) (w : Fin r → ℂ), w ≠ 0 ∧ w ᵥ* A = lam • w := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨lam, hl⟩ := Module.End.exists_eigenvalue (K := ℂ) (A.vecMulLinear : Module.End ℂ (Fin r → ℂ))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  exact ⟨lam, w, hw.2, hw.apply_eq_smul⟩

theorem row_eig_conj (A B u : Matrix (Fin r) (Fin r) ℂ) (hu : u.det ≠ 0) (h : u * A = B * u) (lam : ℂ)
    (w : Fin r → ℂ) (hw : w ≠ 0) (he : w ᵥ* A = lam • w) :
    ∃ w' : Fin r → ℂ, w' ≠ 0 ∧ w' ᵥ* B = lam • w' := by
  have hU : IsUnit u.det := isUnit_iff_ne_zero.2 hu
  refine ⟨w ᵥ* u⁻¹, fun h0 => hw ?_, ?_⟩
  · have := congrArg (· ᵥ* u) h0
    simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul u hU] using this
  · have e : u⁻¹ * B = A * u⁻¹ := by
      calc u⁻¹ * B = u⁻¹ * (B * u) * u⁻¹ := by
            rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv u hU, mul_one]
        _ = A * u⁻¹ := by rw [← h, ← mul_assoc, Matrix.nonsing_inv_mul u hU, one_mul]
    rw [Matrix.vecMul_vecMul, e, ← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul]

end Alg

theorem isIntegral_eig {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
    {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r} (hL : Laws D j Xo c U dict)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) {γ : GL (Fin D.R.r) D.host.E} (hγ : γ ∈ ((U σ).X k).Γ)
    {τ : D.host.E →+* ℂ} (hτ : τ ∈ ((U σ).X k).Ψ) (lam : ℂ) (w : Fin D.R.r → ℂ) (hw : w ≠ 0)
    (he : w ᵥ* (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = lam • w) :
    IsIntegral ℤ ((lam - 1) / l.M) := by
  obtain ⟨G, Λ, g, Λk, u, -, hk, -⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨hG, -, -, hfg, hsp, hu, hΓ, -⟩ := hk k
  obtain ⟨γ', ⟨-, hc⟩, hint⟩ := hΓ γ hγ
  have hdet := det_ne_zero_of_gram τ G (hG ▸ ((U σ).X k).Gm_det) _ (hu τ hτ)
  obtain ⟨w', hw', he'⟩ := row_eig_conj _ _ _ hdet (hint τ hτ) lam w hw he
  have h3 := l.three_le
  exact isIntegral_eig_of_congr _ hfg hsp l.M (by omega) _ hc τ w' hw' lam he'

theorem scalar_eq_one_of_conj : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hG hδ _ γ₂ hγ₂ γ hγ ζ hζ
  rcases Nat.eq_zero_or_pos D.R.r with hr | hr
  · ext a
    exact absurd a.isLt (by omega)
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := hσ₂
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (Data.cmType _ τ).2 h⟩
  have hτ₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ :=
    (((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ).2 ((((hL.unf _ hσ).2.1 k).2 τ).1 hτ)
  have hmul : (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      ζ • ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) := by
    have e : (δ * γ₂ : GL (Fin D.R.r) D.host.E) = MulAut.conj δ γ₂ * δ := by simp
    have e' := congrArg (fun x : GL (Fin D.R.r) D.host.E => (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) e
    simp only [Units.val_mul] at e'
    rw [e', hζ, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul]

  have hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ ζ‖ = 1 := by
    refine norm_eq_one_of_herm hr _ ((U₂ σ₂).X k₂).Gm_det ζ fun v w => ?_
    have hs : Function.Surjective (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 δ.isUnit
    obtain ⟨v, rfl⟩ := hs v
    obtain ⟨w, rfl⟩ := hs w
    have key : ∀ x, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ
        (ζ • (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) =
        (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ ((γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) := by
      intro x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec]
    have h1 := (Data.Γ_stab _ γ hγ).1
    rw [← hG] at h1
    rw [← h1, key, key, hδ, (Data.Γ_stab _ γ₂ hγ₂).1, hδ]

  obtain ⟨lam, w, hw, he⟩ := exists_row_eig hr ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ)
  have hinv : ∀ x : GL (Fin D.R.r) D.host.E, (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ *
      ((x⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = 1 := by
    intro x
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one τ (map_zero τ) (map_one τ)]
  have he1 : lam • w ᵥ* ((γ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = w := by
    rw [← Matrix.smul_vecMul, ← he, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hlam : lam ≠ 0 := by
    rintro rfl
    exact hw (by rw [← he1, zero_smul])
  have ha := isIntegral_eig hL hσ k (inv_mem hγ) hτ lam⁻¹ w hw (by
    rw [eq_inv_smul_iff₀ hlam]; exact he1)
  have hb := isIntegral_eig hL₂ hσ₂ k₂ hγ₂ hτ₂ (τ ζ * lam)
    (w ᵥ* (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) (fun h0 => hw (by
      have := congrArg (· ᵥ* ((δ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) h0
      simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)) (by
      have e : ∀ B : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E, (ζ • B).map τ = τ ζ • B.map τ := by
        intro B; ext a b; simp
      rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, hmul, e, Matrix.map_mul, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, he,
        Matrix.smul_vecMul, smul_smul])
  have h3 := l.three_le
  have h3' := d.l₂.three_le
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hM₂ : (d.l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hMM : (d.l₂.M : ℂ) = l.M * d.pd := by exact_mod_cast hlev.2.1
  have hint : IsIntegral ℤ (τ ((ζ - 1) / l.M)) := by
    have e : τ ((ζ - 1) / l.M) = (lam⁻¹ - 1) / l.M + (d.pd : ℂ) * ((τ ζ * lam - 1) / d.l₂.M) +
        (d.l₂.M : ℂ) * ((lam⁻¹ - 1) / l.M * ((τ ζ * lam - 1) / d.l₂.M)) := by
      have hp : (d.pd : ℂ) ≠ 0 := fun h => hM₂ (by rw [hMM, h, mul_zero])
      rw [map_div₀, map_sub, map_one, map_natCast, hMM]
      field_simp
      ring
    rw [e]
    exact (ha.add ((isIntegral_natCast _).mul hb)).add ((isIntegral_natCast _).mul (ha.mul hb))
  have hint' : IsIntegral ℤ ((ζ - 1) / (l.M : D.host.E)) :=
    (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 hint
  rw [eq_one_of_congr ζ hnorm l.M h3 hint', map_one]

end GlobalTheory.LevScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj

namespace GlobalTheory.KerConjMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_of_ext (D : D7) (δ t0 : ℂ) (σ : D.what₂.LL →+* ℂ) (hfin : (ext D δ t0 σ).Finite) (hne : (ext D δ t0 σ).Nonempty)
    (a n G a' n' G' : ℝ) (ha : a ≤ a') (hn : n ≤ n') (hG : G ≤ G') (x B : ℝ) (hB : 0 ≤ B)
    (h : ∀ ρ ∈ ext D δ t0 σ, x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B) :
    x ≤ Real.exp (a' + n' * avg D δ t0 σ (hArea D δ t0) + G' * avg D δ t0 σ (hTh D δ t0)) * B := by
  obtain ⟨ρ, hρ, h1⟩ := (exists_avg _ hfin hne a' n' G' (hArea D δ t0) (hTh D δ t0)).1
  have hA : 0 ≤ hArea D δ t0 ρ := by unfold hArea; exact Real.posLog_nonneg
  have hT : 0 ≤ hTh D δ t0 ρ := by unfold hTh; exact Real.posLog_nonneg
  calc x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B := h ρ hρ
    _ ≤ Real.exp (a' + n' * hArea D δ t0 ρ + G' * hTh D δ t0 ρ) * B :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) hB

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem mapVV_conj_embLL {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (x : VV D.what₂.LL lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam x) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL lam (mapF (starRingEnd D.what₂.LL) lam x) := by
  rw [mapVV_mapF, embLL_comp_star, mapVV_mapVV]

theorem pairStdAt_of (C b C1 : ℝ)
    (hmA : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hmT : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hfin : ∀ σ : D.what₂.LL →+* ℂ, (ext D ch.S.Z.δ ch.S.Z.t0 σ).Finite ∧ (ext D ch.S.Z.δ ch.S.Z.t0 σ).Nonempty)
    (hRT : RatTopAt ch) (hCT : ConjTopAt ch (C / 2) b C1) (hRR : RatRowAt ch) (hCR : ConjRowAt ch (C / 2) b C1) :
    PairStdAt ch C b := by
  obtain ⟨a1, n1, G1, ha1, hn1, hG1, hs1, hb1⟩ := hCT
  obtain ⟨a2, n2, G2, ha2, hn2, hG2, hs2, hb2⟩ := hCR
  refine ⟨fun p => (a1 + a2) + (n1 + n2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    (G1 + G2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · have eA : aOne ch.G (C / 2) b + aOne ch.G (C / 2) b = aOne ch.G C b := by unfold aOne; ring
    refine (meanInf_affine _ (a1 + a2) (n1 + n2) (G1 + G2) _ _ (by linarith)).trans ?_
    have e1 := mul_le_mul_of_nonneg_left hmA (add_nonneg hn1 hn2)
    have e2 := mul_le_mul_of_nonneg_left hmT (add_nonneg hG1 hG2)
    nlinarith
  · intro p Φ β d hO c
    obtain ⟨hf0, hne⟩ := hfin p.embedding
    refine ⟨fun j B v hv => ?_, fun i B v hv => ?_⟩
    · obtain ⟨f, hf⟩ := hRT Φ β d hO c j
      obtain ⟨u, rfl, hu⟩ := hv
      refine ⟨f u, (hf u).symm, ?_⟩
      exact le_of_ext D _ _ p.embedding hf0 hne a1 n1 G1 _ _ _ (by linarith) (by linarith) (by linarith) _ B
        ((nrm_one_nonneg _ _).trans hu) (fun ρ hρ => hb1 Φ β d hO c j f hf p.embedding ρ hρ u B hu)
    · obtain ⟨f, hf⟩ := hRR Φ β d hO c i
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨mapF (starRingEnd D.what₂.LL) _ (f (mapF (starRingEnd D.what₂.LL) _ w)), ?_, ?_⟩
      · rw [conjMap, mapVV_conj_embLL, hf, mapVV_conj_embLL]
      · have hu : nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (p.embedding.comp (starRingEnd D.what₂.LL)) _
            (mapF (starRingEnd D.what₂.LL) _ w)) ≤ B := by
          rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
        rw [mapVV_mapF]
        exact le_of_ext D _ _ p.embedding hf0 hne a2 n2 G2 _ _ _ (by linarith) (by linarith) (by linarith) _ B
          ((nrm_one_nonneg _ _).trans hw) (fun ρ hρ => hb2 Φ β d hO c i f hf p.embedding ρ hρ _ B hu)

end Std

theorem pairStdK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨F1, k1⟩ := GlobalTheory.T.conjugate_top_bound_of_inputs hP hI hD hDp C1 hC1
  obtain ⟨F2, k2⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  obtain ⟨F3, k3⟩ := GlobalTheory.T.conjugate_row_bound_of_dictionary hP hI hD hDp C1 hC1
  obtain ⟨F4, k4⟩ := GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants
  refine ⟨max (max F1 F2) (max F3 F4), fun CF hCF => ?_⟩
  obtain ⟨C01, l1⟩ := k1 CF (by simp only [max_le_iff] at hCF; exact hCF.1.1)
  obtain ⟨C02, l2⟩ := k2 CF (by simp only [max_le_iff] at hCF; exact hCF.1.2)
  obtain ⟨C03, l3⟩ := k3 CF (by simp only [max_le_iff] at hCF; exact hCF.2.1)
  obtain ⟨C04, l4⟩ := k4 CF (by simp only [max_le_iff] at hCF; exact hCF.2.2)
  refine ⟨2 * max (max C01 C02) (max C03 C04), fun ε C hC => ?_⟩
  have hC' : max (max C01 C02) (max C03 C04) ≤ C / 2 := by linarith
  simp only [max_le_iff] at hC'
  obtain ⟨x1, m1⟩ := l1 ε (C / 2) hC'.1.1
  obtain ⟨x2, m2⟩ := l2 ε (C / 2) hC'.1.2
  obtain ⟨x3, m3⟩ := l3 ε (C / 2) hC'.2.1
  obtain ⟨x4, m4⟩ := l4 ε (C / 2) hC'.2.2
  refine ⟨max (max x1 x2) (max x3 x4), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  exact pairStdAt_of ch C large₂.sc.b C1 hmA hmT
    (fun σ => GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ)
    (m2 D large₂ hε hx.1.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m1 D large₂ hε hx.1.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m4 D large₂ hε hx.2.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m3 D large₂ hε hx.2.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (v : Pl F) (p : UG (cA σ) (dbl (incM F G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  first | exact @GlobalTheory.DblActs.dbl_acts | exact GlobalTheory.DblActs.dbl_acts | (intros; apply GlobalTheory.DblActs.dbl_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAtSurj
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.EmbOnto

theorem embAt_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra c.F C] (φ : E →+* C) :
    ∃ σ : E →+* ℂ, embAt c C σ = φ := by
  have hinj : Function.Injective (fun σ : E →+* ℂ => embAt c C σ) := by
    intro σ τ h
    ext a
    have h1 : embF c σ a = embF c τ a := (algebraMap c.F C).injective (DFunLike.congr_fun h a)
    have h2 := congrArg (fun x : c.F => (x : ℂ)) h1
    exact h2
  have hb := Function.Injective.bijective_of_nat_card_le hinj (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card,
      NumberField.Embeddings.card])
  exact hb.2 φ

end GlobalTheory.EmbOnto
end

