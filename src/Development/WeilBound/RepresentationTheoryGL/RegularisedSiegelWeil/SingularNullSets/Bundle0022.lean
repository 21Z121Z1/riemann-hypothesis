import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0021
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0018
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0772
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem memH {ε : AF F} (h : fixE ε) : ε * h.1 = h.1 := h.2

theorem memY {ε : AF F} (y : (AddMonoidHom.mulLeft ε).ker) : ε * y.1 = 0 := y.2

theorem kdata (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S')
    {ε : AF F} (hε : IsIdF S ε) (db : Measure (AF F)) (ν : Measure (fixE ε)) [SFinite ν]
    (νY : Measure (AddMonoidHom.mulLeft ε).ker) [SFinite νY] (c : ℝ≥0) (hc : 0 < c)
    (hdec : ∀ f : AF F → ℂ,
      (Integrable f db ↔ Integrable (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => f (z.1.1 + z.2.1)) (ν.prod νY)) ∧
      ∫ x, f x ∂db = (c : ℂ) * ∫ z : fixE ε × (AddMonoidHom.mulLeft ε).ker, f (z.1.1 + z.2.1) ∂(ν.prod νY))
    (ρ : Ainf F → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU0 : ∀ v, (0 : Fv F v) ∈ U v)
    (hI : Integrable (fouA ψ db (testT ρ S' U)) db)
    (hinv : ∀ z, ∫ b, fouA ψ db (testT ρ S' U) b * ψ (b * z) ∂db = testT ρ S' U (-z))
    (hne : ∫ y, testT ρ S' U y ∂db ≠ 0) :
    ∃ (g : fixE ε → ℂ) (Gc : ℝ), 0 ≤ Gc ∧ Integrable g ν ∧ (∀ h, ‖g h‖ ≤ 1) ∧
      (∀ s, ∫ h, g h * ψ (h.1 * s) ∂ν = ((Gc * tR ρ S' U (-(ε * s)) : ℝ) : ℂ)) ∧
      ∀ h : fixE ε, g h = fouA ψ db (testT ρ S' U) h.1 / ∫ y, testT ρ S' U y ∂db := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hεε := idF_mul hε
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set τH : fixE ε → ℂ := fun h => ((tR ρ S' U h.1 : ℝ) : ℂ) with hτH
  set τY : (AddMonoidHom.mulLeft ε).ker → ℂ := fun y => ((bR S' U y.1 : ℝ) : ℂ) with hτY
  set A : AF F → ℂ := fun s => ∫ h, τH h * ψ (h.1 * s) ∂ν with hA
  set Bf : AF F → ℂ := fun s => ∫ y, τY y * ψ (y.1 * s) ∂νY with hBf
  have hsplit : ∀ (h : fixE ε) (y : (AddMonoidHom.mulLeft ε).ker), testT ρ S' U (h.1 + y.1) = τH h * τY y := by
    intro h y
    rw [testT_eq, tR_split hSS hε ρ U hU0 (memH h) (memY y)]
    push_cast
    rfl
  have hpm : ∀ (h h0 : fixE ε) (y y0 : (AddMonoidHom.mulLeft ε).ker),
      (h.1 + y.1) * (h0.1 + y0.1) = h.1 * h0.1 + y.1 * y0.1 := by
    intro h h0 y y0
    have h1 : h.1 * y0.1 = 0 := fix_mul_ker hεε (memH h) (memY y0)
    have h2 : y.1 * h0.1 = 0 := by rw [mul_comm]; exact fix_mul_ker hεε (memH h0) (memY y)
    rw [add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add]
  have hfou : ∀ (h0 : fixE ε) (y0 : (AddMonoidHom.mulLeft ε).ker),
      fouA ψ db (testT ρ S' U) (h0.1 + y0.1) = (c : ℂ) * (A h0.1 * Bf y0.1) := by
    intro h0 y0
    simp only [fouA]
    rw [(hdec _).2]
    congr 1
    rw [← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsplit, hpm, AddChar.map_add_eq_mul]
    ring
  have hint : ∫ y, testT ρ S' U y ∂db = (c : ℂ) * ((∫ h, τH h ∂ν) * ∫ y, τY y ∂νY) := by
    rw [(hdec _).2, ← integral_prod_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z.1 z.2)
  set IH := ∫ h, τH h ∂ν with hIH
  set IY := ∫ y, τY y ∂νY with hIY
  have hIH0 : IH ≠ 0 := fun h0 => hne (by rw [hint, h0, zero_mul, mul_zero])
  have hIY0 : IY ≠ 0 := fun h0 => hne (by rw [hint, h0, mul_zero, mul_zero])
  have hτHI : Integrable τH ν := by
    by_contra hn
    exact hIH0 (integral_undef hn)
  have hτR : Integrable (fun h : fixE ε => tR ρ S' U h.1) ν := by
    have := hτHI.norm
    refine this.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [hτH, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tR_nonneg hρ0 S' U _)
  set IHr := ∫ h, tR ρ S' U h.1 ∂ν with hIHr
  have hIHc : IH = (IHr : ℂ) := integral_ofReal
  have hIHr0 : 0 < IHr := by
    refine lt_of_le_of_ne (integral_nonneg fun h => tR_nonneg hρ0 S' U _) fun h0 => hIH0 ?_
    rw [hIHc, ← h0, Complex.ofReal_zero]
  have hA0 : A 0 = IH := by
    simp only [hA, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIH.symm
  have hB0 : Bf 0 = IY := by
    simp only [hBf, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIY.symm
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1

  have hAc : Continuous A := by
    refine continuous_of_dominated (bound := fun h => ‖τH h‖) (fun s => ?_) (fun s => ?_) hτHI.norm ?_
    · exact hτHI.aestronglyMeasurable.mul
        (hψ.1.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun h => by rw [norm_mul, hψn, mul_one]
    · exact Filter.Eventually.of_forall fun h => continuous_const.mul (hψ.1.comp (continuous_const.mul continuous_id))

  set IB := ∫ y, Bf y.1 ∂νY with hIB
  have hinvH : ∀ s, ε * s = s →
      ((tR ρ S' U (-s) : ℝ) : ℂ) = (c : ℂ) ^ 2 * IB * ∫ h, A h.1 * ψ (h.1 * s) ∂ν := by
    intro s hs
    have h1 := hinv s
    rw [(hdec _).2, testT_eq] at h1
    have h2 : ∀ z : fixE ε × (AddMonoidHom.mulLeft ε).ker,
        fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1) * ψ ((z.1.1 + z.2.1) * s) =
          ((c : ℂ) * (A z.1.1 * ψ (z.1.1 * s))) * Bf z.2.1 := by
      intro z
      have hz : z.2.1 * s = 0 := by rw [mul_comm]; exact fix_mul_ker hεε hs (memY z.2)
      rw [hfou, add_mul, hz, add_zero]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_prod_mul (fun h : fixE ε => (c : ℂ) * (A h.1 * ψ (h.1 * s))) (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1),
      integral_const_mul] at h1
    rw [← h1]
    ring

  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : fixE ε, tR ρ S' U h₀.1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hIHr0.ne'
    rw [hIHr]
    simp [hn]
  have hIB0 : IB ≠ 0 := by
    intro h0
    have h1 := hinvH (-h₀.1) (by rw [mul_neg, memH h₀])
    rw [neg_neg, h0, mul_zero, zero_mul] at h1
    exact hh₀ (by exact_mod_cast h1)
  set κ : ℂ := ((c : ℂ) ^ 2 * IB)⁻¹ with hκ
  have hcB : (c : ℂ) ^ 2 * IB ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) hIB0
  have hinvG : ∀ s, ∫ h, A h.1 * ψ (h.1 * s) ∂ν = κ * ((tR ρ S' U (-(ε * s)) : ℝ) : ℂ) := by
    intro s
    have hes : ε * (ε * s) = ε * s := by rw [← mul_assoc, hεε]
    have h1 : ∀ h : fixE ε, h.1 * s = h.1 * (ε * s) := fun h => by
      conv_lhs => rw [← memH h]
      ring
    simp only [h1]
    rw [hinvH _ hes, hκ, ← mul_assoc, inv_mul_cancel₀ hcB, one_mul]

  have hAI : Integrable (fun h : fixE ε => A h.1) ν := by
    have h1 := (hdec (fouA ψ db (testT ρ S' U))).1.1 hI
    have h2 : (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1)) =
        fun z => (c : ℂ) * (A z.1.1 * Bf z.2.1) := funext fun z => hfou z.1 z.2
    rw [h2] at h1
    have hBI : Integrable (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1) νY := by
      by_contra hn
      exact hIB0 (integral_undef hn)
    have hK : 0 < ∫ y, ‖Bf y.1‖ ∂νY :=
      lt_of_lt_of_le (norm_pos_iff.2 hIB0) (norm_integral_le_integral_norm _)
    have h3 := ((integrable_prod_iff h1.aestronglyMeasurable).1 h1).2
    have h4 : ∀ h : fixE ε, ∫ y, ‖(c : ℂ) * (A h.1 * Bf y.1)‖ ∂νY =
        (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY) * ‖A h.1‖ := by
      intro h
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_const_mul]
      ring
    simp only [h4] at h3
    have hcK : ‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hc0) hK.ne'
    have h5 : Integrable (fun h : fixE ε => ‖A h.1‖) ν := by
      refine (h3.const_mul (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY)⁻¹).congr (Filter.Eventually.of_forall fun h => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hcK, one_mul]
    exact (integrable_norm_iff (hAc.comp continuous_subtype_val).aestronglyMeasurable).1 h5

  obtain ⟨M, hM⟩ := hρc.bddAbove_range_of_hasCompactSupport hρs
  have hτM : ∀ h : fixE ε, tR ρ S' U h.1 ≤ M := by
    intro h
    have hρM : ρ (fstA F h.1) ≤ M := hM ⟨_, rfl⟩
    unfold tR
    by_cases hb : sndA F h.1 ∈ boxA S' U
    · rw [Set.indicator_of_mem hb, mul_one]; exact hρM
    · rw [Set.indicator_of_notMem hb, mul_zero]; exact (hρ0 _).trans hρM
  have hk := kappa_real ψ hψ ν (fun h => tR ρ S' U h.1) (fun h => tR_nonneg hρ0 S' U _) hτR hIHr0 M hτM
    (fun h => A h.1) (fun s => rfl) hAI κ (fun s => by
      have := hinvG s.1
      rw [memH s] at this
      exact this)
  have hAb : ∀ s, ‖A s‖ ≤ IHr := by
    intro s
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hIHr]
    congr 1
    funext h
    rw [norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_of_nonneg (tR_nonneg hρ0 S' U _)]
  have hκr : κ = (κ.re : ℂ) := Complex.ext (by simp) (by simp [hk.1])
  have hIHr0' : (IHr : ℂ) ≠ 0 := by exact_mod_cast hIHr0.ne'
  refine ⟨fun h => A h.1 / IH, κ.re / IHr, div_nonneg hk.2 hIHr0.le, hAI.div_const _, fun h => ?_, fun s => ?_,
    fun h => ?_⟩
  · rw [norm_div, hIHc, Complex.norm_real, Real.norm_of_nonneg hIHr0.le]
    exact (div_le_one hIHr0).2 (hAb _)
  · simp_rw [div_mul_eq_mul_div]
    rw [integral_div, hinvG, hIHc, hκr]
    push_cast
    field_simp
    rw [Complex.ofReal_re]
    ring
  · have h1 := hfou h 0
    rw [ZeroMemClass.coe_zero, add_zero, hB0] at h1
    simp only
    rw [h1, hint]
    field_simp

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem theta_levi {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hω.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), GlobalTheory.CompanionTheory.ThetaInv.psi_unip_rat hψ, one_mul]

open GlobalTheory.CompanionTheory.ThetaPoisson in
theorem theta_weyl {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (hω : IsWeilSch ψ χ θ V μ ω) (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv' {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi hχ hω g a hg Φ)
    (fun g b hg Φ => theta_unip hψ hω g b hg Φ)
    (fun g hg Φ => theta_weyl hψ hθ hμ hω g hg Φ)
  exact hle hγ Φ

theorem theta_rat {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) (g : G D n) (h : GA D V) : theta ω Φ (γ * g) h = theta ω Φ g h := by
  have hc := (GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω h⁻¹).2 γ (ω g Φ)
    (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) (fun _ => rfl)
  have ht := thetaInv' hψ hχ hθ hμ hω (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) hγ
  simp only [hc] at ht
  unfold theta
  rw [map_mul, Module.End.mul_apply]
  exact ht

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

