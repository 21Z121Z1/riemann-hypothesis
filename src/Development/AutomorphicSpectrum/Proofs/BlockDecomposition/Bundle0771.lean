import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0765
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0764
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AutomorphicSpectrum.Proofs.HermitianForms.ExistsIsCharAFOfStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNonnegReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem good_rows {S : Finset (Pl D)} {e : AE D} {η : Fin a → Mx D 1 b → ℂ} (h : ∀ i, Good S e (η i)) :
    Good S e (fun y : Mx D a b => ∏ i, η i (y.submatrix (fun _ => i) id)) := by
  intro y
  by_cases hy : IntOff S y
  · rw [if_pos hy]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : IntOff S (y.submatrix (fun _ : Fin 1 => i) id) := fun v hv _ j => hy v hv i j
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_pos hi] at this
    exact this
  · rw [if_neg hy]
    simp only [IntOff] at hy
    push Not at hy
    obtain ⟨v, hv, i, j, hij⟩ := hy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_neg (fun hi => hij (hi v hv 0 j))] at this
    exact this

theorem prod_nonneg_real {ι : Type} (s : Finset ι) (w : ι → ℂ) (h : ∀ i, 0 ≤ (w i).re ∧ (w i).im = 0) :
    0 ≤ (∏ i ∈ s, w i).re ∧ (∏ i ∈ s, w i).im = 0 := by
  refine Finset.prod_induction w (fun x : ℂ => 0 ≤ x.re ∧ x.im = 0) ?_ (by simp) fun i _ => h i
  rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  simp [Complex.mul_re, Complex.mul_im, hx', hy', mul_nonneg hx hy]

theorem blockMatrix_add_zero {R : Type} (A : Matrix (Fin t) (Fin t) R) (b' : Matrix (Fin t) (Fin 0) R) (c : Matrix (Fin 0) (Fin t) R)
    (d : Matrix (Fin 0) (Fin 0) R) : bl (add_zero t) A b' c d = A := by
  have h : ∀ i : Fin t, (finSumFinEquiv.trans (finCongr (add_zero t))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rfl
  ext i j
  simp only [bl, Matrix.submatrix_apply, h, Matrix.fromBlocks_apply₁₁]

theorem exists_isW (D : D7) (t : ℕ) : ∃ w : G D t, IsW w := by
  obtain ⟨⟨M⟩, -⟩ := GlobalTheory.CompanionTheory.JacobiMaps.mapsExist D t t 0 (add_zero t)
  refine ⟨M.w, ?_⟩
  have := M.w_mat
  simp only [blockMatrix_add_zero] at this
  exact this

theorem rsec_inv {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D r)
    {θ : InfFam D} (ω : G D n →* Module.End ℂ (schwartzA θ a n)) (Φ : schwartzA θ a n) {Ω : G D t → Mx D r t → ℂ} (u : G D t)
    (h1 : ω (M.emb u) Φ = Φ) (h2 : ∀ h, Ω (h * u) = Ω h) (g : G D t) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (g * u) = Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω g := by
  have hf : ∀ x, (ω (x * M.emb u) Φ).1 0 = (ω x Φ).1 0 := fun x => by
    rw [map_mul, Module.End.mul_apply, h1]
  have e1 : ∀ y z, M.w * M.nzx z 0 * (M.sh y * M.emb (g * u) * 1) =
      (M.w * M.nzx z 0 * (M.sh y * M.emb g * 1)) * M.emb u := fun y z => by
    rw [map_mul]
    simp only [mul_one, mul_assoc]
  simp only [Rsec, Wz, h2, e1, hf]

section Xi

variable (V : HSp D) (b₀ : HermE D r) (hn : r + t = n)

def xiP (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (z : Mx D V.rank r × Mx D V.rank t) : ℂ :=
  Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z))

variable {V b₀ hn}

theorem continuous_xiP {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Continuous Φ) (hη : Continuous η) : Continuous (xiP V b₀ hn Φ η) := by
  have hy := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ (0 : hermA D t)).2.1
  exact (hΦ.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hη.comp hy))

theorem xiP_cond {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Good S e Φ) (hη : Good S e η)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    (p : Mx D V.rank r × Mx D V.rank t → ℂ) (hp : ∀ z, p (e • z.1, e • z.2) = p z) (z : Mx D V.rank r × Mx D V.rank t) :
    (IntOff S z.1 ∧ IntOff S z.2 → xiP V b₀ hn Φ η z * p z = xiP V b₀ hn Φ η (e • z.1, e • z.2) * p (e • z.1, e • z.2)) ∧
      (¬ (IntOff S z.1 ∧ IntOff S z.2) → xiP V b₀ hn Φ η z * p z = 0) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_pos ((intOff_jn hn _ _).2 ⟨h1, h2⟩), jn_smul] at a1
    have a2 := hη (yv V b₀ z)
    rw [if_pos (hy z h1 h2), ← yv_smul he hc] at a2
    rw [hp]
    simp only [xiP]
    rw [a1, a2]
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_neg (fun hh => h ((intOff_jn hn _ _).1 hh))] at a1
    simp [xiP, a1]

set_option synthInstance.maxHeartbeats 400000 in

theorem cell_id {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) [BorelSpace (Mx D V.rank r × Mx D V.rank t)]
    {P : Measure (Mx D V.rank r × Mx D V.rank t)} {σ : Measure (XS D V.rank r t e)}
    (hL : ∀ Ξ : Mx D V.rank r × Mx D V.rank t → ℂ, Continuous Ξ →
      (∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) →
      (Integrable Ξ P → Integrable (fun z : XS D V.rank r t e => Ξ z.1) σ) ∧ ∫ z, Ξ z ∂P = ∫ z : XS D V.rank r t e, Ξ z.1 ∂σ)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ} (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ) (hη : Good S e η)
    {B : ℝ} (hB : ∀ y, ‖η y‖ ≤ B) (hI : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => Φ (jn hn z.1 z.2)) P) :
    Integrable (fun z : XS D V.rank r t e => xiP V b₀ hn Φ η z.1) σ ∧
      ∀ x : hermS D t e, ∫ z, xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z) ∂P =
        ∫ z : XS D V.rank r t e, xiP V b₀ hn Φ η z.1 * pch ψ x.1.1 (qv V b₀ z.1) ∂σ := by
  have hx := continuous_xiP (b₀ := b₀) (hn := hn) hψ hΦc hηc
  haveI : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  constructor
  · have hc1 := xiP_cond (hn := hn) he hc hΦ hη hy (fun _ => 1) (fun _ => rfl)
    simp only [mul_one] at hc1
    refine (hL _ hx hc1).1 ?_
    refine (hI.norm.const_mul B).mono' hx.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [xiP, norm_mul, RCLike.norm_conj]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · intro x
    have hcp := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ x.1).2.2.2.1
    refine (hL (fun z => xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z)) (hx.mul hcp) ?_).2
    refine xiP_cond (hn := hn) he hc hΦ hη hy _ fun z => ?_
    rw [qv_smul he hc]
    exact pch_smul x.2 _

end Xi

end GlobalTheory.CompanionTheory.EisE

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem hecke_one : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩

theorem hecke_mul_inv {χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ') : IsHeckeChar D (1 * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have e : (⇑((1 : (AE D)ˣ →* Circle) * χ'⁻¹)) = fun x => (χ' x)⁻¹ := by
      funext x; simp
    rw [e]
    exact h.1.inv
  · simpa using h.2 x

theorem fj_smul {n ρ p' : ℕ} {hn : ρ + p' = n} (M : Maps D hn) (m : Meas D ρ p') (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (c : ℂ) (F : G D n → ℂ) (g : G D n) (φ : Mx D ρ p' → ℂ) :
    FJ M m ψ b₀ (c • F) g φ = c * FJ M m ψ b₀ F g φ := by
  simp only [FJ, PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem eis_pole_free (hRS : RSec) (hEH : EisHol) (hp : 2 ≤ p) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn) (m : Meas D 1 p')
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ' : (AE D)ˣ →* Circle} (hχ' : IsHeckeChar D χ') {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p' → Mx D 1 p' → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (g : G D p) :
    Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) (σ : ℂ)) g Ω) 1)
      (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
  obtain ⟨c1, c2, c3⟩ := hRS D p 1 p' hn M m ψ hψ b₀ hdet 1 χ' hecke_one hχ' θ hθ Ω hΩ H hH ((p : ℂ) / 2) f hf.1 hf.2 g
  have hd := hEH D p' (1 * χ'⁻¹) (hecke_mul_inv hχ') _ (fun z => Rsec M m ψ b₀ (fam H f ((p : ℂ) / 2) z) g Ω) c1 c2 c3 1
  have hopen : IsOpen {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_re)
  have hpp : (p : ℝ) = 1 + p' := by rw [← hn]; push_cast; ring
  have hp' : (1 : ℝ) ≤ p' := by
    have : 1 ≤ p' := by omega
    exact_mod_cast this
  have hmem : ((((p : ℝ) / 2 : ℝ)) : ℂ) ∈ {z : ℂ | (((1 : ℕ) : ℝ) - p') / 2 < z.re ∧ (p' : ℝ) / 2 < z.re} := by
    simp only [mem_setOf_eq, Complex.ofReal_re, hpp, Nat.cast_one]
    constructor <;> linarith
  have hcont := (hd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have h1 := (hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt (x := (p : ℝ) / 2))).mono_left
    (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
  have h2 : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ)) (𝓝[>] ((p : ℝ) / 2)) (𝓝 0) := by
    have : Continuous fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) := by fun_prop
    have h3 := (this.tendsto ((p : ℝ) / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi ((p : ℝ) / 2)))
    simpa using h3
  simpa using h2.mul h1

theorem pc_vanish (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal) (hS : SphBound)
    (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {p' : ℕ} (hn : 1 + p' = p) (M : Maps D hn)
    (m : Meas D 1 p') (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (b₀ : HermE D 1) (hb : IsDiagInv b₀) (g : G D p) : pc M m ψ b₀ (resA H f) g = 0 := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨χ', hχ', hres⟩ := hHE D 1
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  have hU := ufil_le p
  have key : ∀ g₀ : G D p, (fun y => pc M m ψ b₀ (resA H f) (M.sh y * g₀)) = 0 := fun g₀ => by
    refine hTT D 1 p' m ψ hψ b₀ hb χ' hχ' hres (fun h => absurd h one_ne_zero) θ hθ _ ?_ ?_ ?_
    · exact ((hPB D p 1 p' hn M m ψ hψ b₀).1 _ hAc hAl).comp (M.sh_cont.mul continuous_const)
    · obtain ⟨C₁, hC₁, -, hb₁⟩ := (hPB D p 1 p' hn M m ψ hψ b₀).2 g₀
      obtain ⟨B, hB⟩ := hC₁.exists_bound_of_continuousOn hAc.continuousOn
      exact ⟨B, hb₁ _ hAc hAl B hB⟩
    · intro Ω hΩ
      have hint : Integrable (Ω 1) m.μ := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ 1 p' m.μ m.𝓕 m.hμ (Ω 1) (hΩ.mem 1)
      have hFl : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), Continuous (res H f σ) ∧ LeftInv (GF D p) (res H f σ) := by
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ using ⟨res_cont hS hp1 hH hC hcov hf hσ, res_leftInv hH hf σ⟩
      have hlim := GlobalTheory.T.partial_coefficient_uniform_limit hPB D p 1 p' hn M m ψ hψ b₀ ((ufil p : Ultrafilter ℝ) : Filter ℝ) (fun σ => res H f σ) (resA H f)
        hAc hAl hFl (fun C' hC' ε hε => resA_unif hS hp1 hH hC hcov hf hC' hε)
        (hFl.mono fun σ hσ y g' => GlobalTheory.T.partial_coefficient_sub hPB D p 1 p' hn M m ψ hψ b₀ _ _ hσ.1 hσ.2 hAc hAl y g') g₀ (Ω 1) hint
      have hzero : Tendsto (fun σ => FJ M m ψ b₀ (res H f σ) g₀ (Ω 1)) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 0) := by
        refine ((eis_pole_free hRS hEH hp hn M m ψ hψ b₀ hb.2 hχ' hθ hΩ hH hf g₀).mono_left hU).congr' ?_
        refine hU ?_
        filter_upwards [ev_Ioc p] with σ hσ
        have e : res H f σ = ((σ - p / 2 : ℝ) : ℂ) • eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) := rfl
        rw [e, fj_smul, hFJ D p 1 p' hn M m ψ hψ b₀ hb.2 1 χ' hecke_one hχ' θ hθ Ω hΩ (σ : ℂ) _
          (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) (by simpa using hσ.1) g₀]
      exact tendsto_nhds_unique hlim hzero
  have := congrFun (key ((M.sh 0)⁻¹ * g)) 0
  simpa [← mul_assoc] using this

theorem resA_n_inv (hME : MapsExist) (hHE : HeckeEta) (hFJ : FJEis) (hPB : PcBound) (hRS : RSec) (hEH : EisHol) (hTT : ThTotal)
    (hPF : PcFc) (hS : SphBound) (hp : 2 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {nb : hermA D p → G D p}
    {lam : Measure (hermA D p)} {𝓖 : Set (hermA D p)} (hCd : CoefData (D := D) (n := p) nb lam 𝓖) (b : hermA D p) (g : G D p) :
    resA H f (nb b * g) = resA H f g := by
  have hp1 : 1 ≤ p := by omega
  have hAc := resA_cont hS hp1 hH hC hcov hf
  have hAl := resA_leftInv hS hp1 hH hC hcov hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.AdelicChar.exists_isCharAF D.host.F D.sp.cm.totReal
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hn : 1 + (p - 1) = p := by omega
  obtain ⟨⟨M⟩, ⟨m⟩⟩ := hME D p 1 (p - 1) hn
  obtain ⟨⟨M0⟩, ⟨m0⟩⟩ := hME D p 0 p (zero_add p)
  have hr : RankLT ψ (resA H f) 1 := (hPF D p 1 (p - 1) hn M m ψ hψ _ hAc hAl).1 fun b₀ hb g =>
    pc_vanish hHE hFJ hPB hRS hEH hTT hS hp hH hC hcov hf hn M m ψ hψ hθ b₀ hb g
  let b0 : HermE D 0 := ⟨0, by ext i; exact i.elim0⟩
  let β : HermE D p := ⟨0, by simp⟩
  have hdet : b0.1.det ≠ 0 := by simp [b0]
  have hβ : IsExt (zero_add p) b0 β := by
    ext i j
    simp only [bl, Matrix.submatrix_apply, β]
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm i = a
    generalize (finSumFinEquiv.trans (finCongr (zero_add p))).symm j = c
    rcases a with a | a
    · exact a.elim0
    · rcases c with c | c
      · exact c.elim0
      · simp
  have h2 := (hPF D p 0 p (zero_add p) M0 m0 ψ hψ _ hAc hAl).2 hr b0 hdet β hβ nb lam 𝓖 hCd
  exact GlobalTheory.T.invariance_of_constant_fourier_coefficient D p ψ nb lam 𝓖 hCd _ hAc hAl β rfl (fun g => by
    rw [← h2 g]; exact GlobalTheory.T.partial_coefficient_rank_zero D p (zero_add p) M0 m0 ψ b0 _ g) b g

theorem resMu_main : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound →
    PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  intro hME hHt hHE hFJ hPB hRS hEH hTT hPF hS _ hCE D p hp
  have hp1 : 1 ≤ p := by omega
  obtain ⟨⟨H, hH⟩, C, hC, hcov⟩ := hHt D p
  refine ⟨fun f => resA H f 1, ?_⟩
  exact
    { add := fun f f' hf hf' => resA_add hS hp1 hH hC hcov hf hf' 1
      smul := fun c f hf => resA_smul hS hp1 hH hC hcov hf c 1
      pos := fun f hf h => resA_pos hS hp1 hH hC hcov hf h 1
      bound := fun H' hH' => resA_bound hS hp1 hH hC hcov H' hH'
      inv_n := fun x b hx f hf => by
        have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨x, hx⟩
        obtain ⟨nb, lam, 𝓖, hCd⟩ := hCE D p
        have e : x = nb ⟨b, hb⟩ * 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by rw [mul_one, hx, hCd.1])
        have h1 := resA_translate hS hp1 hH hC hcov hf x
        have h2 := resA_n_inv hME hHE hFJ hPB hRS hEH hTT hPF hS hp hH hC hcov hf hCd ⟨b, hb⟩ 1
        rw [← e] at h2
        exact h1.symm.trans h2
      inv_rat := fun γ hγ f hf => by
        have h1 := resA_translate hS hp1 hH hC hcov hf γ
        have h2 := resA_leftInv hS hp1 hH hC hcov hf γ hγ 1
        rw [mul_one] at h2
        exact h1.symm.trans h2
      lim := fun f hc hl a ha => (resA_lim hS hp1 hH hC hcov f hc hl a ha).2 }

end GlobalTheory.CompanionTheory.ResMu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatrices
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem coY_sum_mul_eq_zero : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 →
    ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β →
      ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  intro k _ _ n ψ₀ hψ β T hne
  classical
  let χ : AddChar (Matrix (Fin n) (Fin n) k) ℂ :=
    { toFun := fun Y => ψ₀ (Matrix.trace (Y * (T - β)))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun X Y => by
        rw [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul] }
  have hχ : χ ≠ 1 := by
    have hA : T - β ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i, j, hij⟩ : ∃ i j, (T - β) i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hA (Matrix.ext h)
    obtain ⟨a, ha⟩ := (AddChar.ne_one_iff).1 hψ
    refine (AddChar.ne_one_iff).2 ⟨Matrix.single j i (a / (T - β) i j), ?_⟩
    have htr : Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β)) = a := by
      rw [Matrix.trace_single_mul]
      exact div_mul_cancel₀ a hij
    change ψ₀ (Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β))) ≠ 1
    rw [htr]
    exact ha
  have hterm : ∀ Y : Matrix (Fin n) (Fin n) k,
      coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * χ Y := by
    intro Y
    have hχY : χ Y = ψ₀ (Matrix.trace (Y * (T - β))) := rfl
    rw [coY, hχY, ← AddChar.map_neg_eq_conj, mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub,
      Matrix.trace_sub]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun Y _ => hterm Y), ← Finset.mul_sum, AddChar.sum_eq_zero_of_ne_one hχ, mul_zero]

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

abbrev rt (ξ : Matrix (Fin ρ) (Fin p) D.host.E) : Mx D ρ p := ξ.map (incA D)

def chv (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y : Mx D ρ p) : ℂ :=
  ψ (trA (Matrix.trace (pr b₀ x y)))

def jc (y x : Mx D ρ p) : hermA D ρ :=
  ⟨(HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ), by
    have key : ∀ a b : Mx D ρ p, adj (HMul.hMul a (adj b) : Mx D ρ ρ) = (HMul.hMul b (adj a) : Mx D ρ ρ) := by
      intro a b
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
        Formalism.L2.Theta.cA_cA]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    show adj _ = _
    have : adj ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ)) = adj (HMul.hMul y (adj x) : Mx D ρ ρ) + adj (HMul.hMul x (adj y) : Mx D ρ ρ) := by
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add]
    rw [this, key, key, add_comm]⟩

def dsum (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) : ℂ :=
  ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * Φ (rt ξ + y)

def Ap (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (v : Mx D ρ p × Mx D ρ p) : ℂ :=
  dsum ψ b₀ Φ v.2 v.1 * conj (dsum ψ b₀ φ v.2 v.1)

theorem th_zero (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) :
    th ψ b₀ φ 0 x y = dsum ψ b₀ φ x y := by
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have : (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) (0 : hermA D ρ).1 : Mx D ρ ρ)) = 0 := by
      simp
    rw [chz, this]
    simp [halfTr, trA]
  rw [th, h0, one_mul]
  rfl

theorem tsum_meas {ι X : Type} [Countable ι] [MeasurableSpace X] {f : ι → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a := by
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) a => ∑ i ∈ s, f i a) (fun s => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hf i
  · exact tendsto_pi_nhds.2 fun a => (hs a).hasSum

end GlobalTheory.CompanionTheory.FJE
end
end

