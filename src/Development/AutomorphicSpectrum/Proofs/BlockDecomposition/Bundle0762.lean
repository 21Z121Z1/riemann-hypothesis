import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitOfRetract
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0755
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0753
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0760
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mem_cell_iff {e : AE D} (hee : e * e = e) (g : G D p) : g ∈ cell e ↔ InCell e g :=
  isUnit_mix_iff hee (cB g)

theorem continuous_cB : Continuous (cB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem continuous_dB : Continuous (dB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem cell_eq {e : AE D} (hee : e * e = e) :
    cell e = (fun g : G D p => (cB g).det) ⁻¹' {z : AE D | IsUnit (1 - e + e * z)} := by
  ext g
  change IsUnit _ ↔ IsUnit _
  rw [det_mix_one hee]

open Classical in

def tau (e : AE D) (g : G D p) : hermS D p e := if h : ∃ x, IsB e g x then h.choose else 0

theorem isB_tau {e : AE D} {g : G D p} (h : ∃ x, IsB e g x) : IsB e g (tau e g) := by
  rw [tau, dif_pos h]
  exact h.choose_spec

theorem tau_eq {e : AE D} {g : G D p} {x : hermS D p e} (h : IsB e g x) : tau e g = x :=
  isB_unique (isB_tau ⟨x, h⟩) h

theorem tau_formula {e : AE D} (hee : e * e = e) {g : G D p} {x : hermS D p e} (hu : g ∈ cell e) (h : IsB e g x) :
    Ring.inverse (1 - e + e * (cB g).det) • (((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g)) = x.1.1 := by
  have hu' : IsUnit (1 - e + e * (cB g).det) := by
    have := hu
    rw [cell_eq hee] at this
    exact this
  exact mix_solve hee hu' x.2 h.2

theorem continuousOn_tau {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (hee : e * e = e) (hce : cA D e = e) :
    ContinuousOn (tau e : G D p → hermS D p e) (cell e) := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hd : Continuous fun g : G D p => (cB g).det := continuous_cB.matrix_det
  have h1 : ContinuousOn (fun g : G D p => Ring.inverse (1 - e + e * (cB g).det)) (cell e) := by
    refine (unit_AE he).2.comp hd.continuousOn ?_
    intro g hg
    rw [cell_eq hee] at hg
    exact hg
  have h2 : Continuous fun g : G D p => ((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g) := by
    refine Continuous.matrix_mul (Continuous.matrix_adjugate ?_) (continuous_dB.const_smul e)
    exact continuous_const.add (continuous_cB.const_smul e)
  have h3 : ContinuousOn (fun g : G D p => ((tau e g).1.1 : Mx D p p)) (cell e) := by
    refine (h1.smul h2.continuousOn).congr fun g hg => ?_
    have hB : IsB e g (tau e g) := isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
    exact (tau_formula hee hg hB).symm
  have i1 : Topology.IsInducing (Subtype.val : hermS D p e → hermA D p) := Topology.IsInducing.subtypeVal
  have i2 : Topology.IsInducing (Subtype.val : hermA D p → Mx D p p) := Topology.IsInducing.subtypeVal
  exact (i2.comp i1).continuousOn_iff.2 h3

theorem cellAlg : IdemEx → CellAlg := by
  intro hI D p nb hnb w hw S e he
  obtain ⟨hee, hce⟩ := (hI D S).2 e he
  have hex : ∀ g ∈ cell (p := p) e, IsB e g (tau e g) := fun g hg =>
    isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
  have hcell : ∀ {g : G D p} {x : hermS D p e}, IsB e g x → g ∈ cell e := fun h => (mem_cell_iff hee _).2 h.1
  refine ⟨tau e, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, continuousOn_tau he hee hce, (continuous_nb hnb).comp continuous_subtype_val,
      fun x y => isNMap_add hnb x.1 y.1⟩
    · rw [cell_eq hee]
      exact (unit_AE he).1.preimage (continuous_cB.matrix_det (R := AE D))
    · intro q hq x hx
      have h := (LeftCell.isB_left hq (tau e x)).2 (hex x hx)
      exact ⟨hcell h, (tau_eq h)⟩
    · intro y x hx
      have h := (isB_mul_nb hnb y (tau e x)).2 (hex x hx)
      exact ⟨hcell h, tau_eq h⟩
  · intro g hg u hu
    exact hcell ((isB_mul_right_iff he hu (tau e g)).2 (hex g hg))
  · intro g hg
    have h := hex g hg
    change (e • cB g) * _ = _
    rw [smul_mul_assoc]
    have h2 : cB g * (tau e g).1.1 = e • dB g := h.2
    rw [h2, smul_smul, hee]

end GlobalTheory.CompanionTheory.CellTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPartialFourierMean
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

open GlobalTheory.CompanionTheory.PcB (chz_norm continuous_chz)

variable {D : D7} {n ρ p : ℕ}

theorem continuous_adjMx : Continuous (adj : Mx D ρ p → Mx D p ρ) :=
  Continuous.matrix_transpose (Continuous.matrix_map continuous_id GlobalTheory.AnnihBox.continuous_cA')

theorem continuous_bT (hn : ρ + p = n) :
    Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => bT hn u.1 u.2.1 u.2.2 := by
  have h1 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.1 : Mx D ρ ρ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => u.2.1 :=
    continuous_fst.comp continuous_snd
  have h3 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => adj u.2.1 :=
    continuous_adjMx.comp h2
  have h4 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.2.2 : Mx D p p) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hbl : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p =>
      bl hn (u.1 : Mx D ρ ρ) u.2.1 (adj u.2.1) (u.2.2 : Mx D p p) := by
    unfold bl
    exact (Continuous.matrix_fromBlocks h1 h2 h3 h4).matrix_submatrix _ _
  unfold bT
  exact hbl.subtype_mk _

theorem exists_bound_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) :
    ∃ B : ℝ, ∀ x, ‖Φ x‖ ≤ B := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨γ, hγ, hγx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hB _ hγx

private theorem eventually_uniform_continuity_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ a, ‖Φ (a + v) - Φ a‖ < ε := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  have hc : Continuous fun w : hermA D n × hermA D n => ‖Φ (w.2 + w.1) - Φ w.2‖ :=
    ((hΦ.comp (continuous_snd.add continuous_fst)).sub (hΦ.comp continuous_snd)).norm
  have hev : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ k ∈ K, ‖Φ (k + v) - Φ k‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : ‖Φ (k + 0) - Φ k‖ < ε := by
      simpa using hε
    exact (hc.tendsto ((0 : hermA D n), k)).eventually (gt_mem_nhds h0)
  filter_upwards [hev] with v hv a
  obtain ⟨γ, hγ, hγa⟩ := hcov a
  have h1 := hv _ hγa
  rwa [add_assoc, hper γ hγ, hper γ hγ] at h1

private theorem bT_add (hn : ρ + p = n) (z z' : hermA D ρ) (x x' : Mx D ρ p) (y y' : hermA D p) :
    bT hn (z + z') (x + x') (y + y') = bT hn z x y + bT hn z' x' y' := by
  apply Subtype.ext
  show bl hn (z + z').1 (x + x') (GlobalTheory.MixModel.adj (x + x')) (y + y').1 =
    bl hn z.1 x (GlobalTheory.MixModel.adj x) y.1 + bl hn z'.1 x' (GlobalTheory.MixModel.adj x') y'.1
  rw [GlobalTheory.CompanionTheory.PcB.blockMatrix_add', GlobalTheory.MixModel.adj_add]
  rfl

theorem continuous_pm (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (hΦ : Continuous Φ)
    (hper : IsPer Φ) : Continuous (pm hn m ψ b₀ Φ) := by
  obtain ⟨B, hB⟩ := exists_bound_of_isPer Φ hΦ hper
  have hchz := continuous_chz hψ b₀
  have hnorm := chz_norm hψ b₀
  obtain ⟨-, -, hz1⟩ := m.hz
  obtain ⟨-, -, hμ1⟩ := m.hμ
  have hlz : m.lz.restrict m.𝓖 Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, hz1]; exact ENNReal.one_lt_top
  have hμf : m.μ.restrict m.𝓕 Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨hlz⟩
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨hμf⟩
  have hrz : (m.lz.restrict m.𝓖 Set.univ).toReal = 1 := by
    rw [Measure.restrict_apply_univ, hz1, ENNReal.toReal_one]
  have hrμ : (m.μ.restrict m.𝓕 Set.univ).toReal = 1 := by
    rw [Measure.restrict_apply_univ, hμ1, ENNReal.toReal_one]
  haveI : OpensMeasurableSpace (Mx D ρ ρ) := ⟨le_rfl⟩
  haveI : OpensMeasurableSpace (Mx D ρ p) := ⟨le_rfl⟩
  haveI : OpensMeasurableSpace (hermA D ρ) :=
    Subtype.opensMeasurableSpace (hermA D ρ : Set (Mx D ρ ρ))
  have hb0 : bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (0 : hermA D p) = 0 := by
    simpa using bT_add hn (0 : hermA D ρ) 0 (0 : Mx D ρ p) 0 (0 : hermA D p) 0
  have hgb : ∀ (x : Mx D ρ p) (y : hermA D p) (z : hermA D ρ),
      ‖Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro x y z
    rw [norm_mul, Complex.norm_conj, hnorm, mul_one]
    exact hB _
  have hmz : ∀ (x : Mx D ρ p) (y : hermA D p),
      AEStronglyMeasurable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := by
    intro x y
    have hc : Continuous fun z : hermA D ρ => ((z, (x, y)) : hermA D ρ × Mx D ρ p × hermA D p) :=
      continuous_id.prodMk continuous_const
    exact ((hΦ.comp ((continuous_bT hn).comp hc)).mul
      (Complex.continuous_conj.comp hchz)).aestronglyMeasurable
  have hint : ∀ (x : Mx D ρ p) (y : hermA D p),
      Integrable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := fun x y =>
    (integrable_const B).mono' (hmz x y) (ae_of_all _ fun z => hgb x y z)
  have hE : ∀ (y y' : hermA D p) (x x' : Mx D ρ p) (δ : ℝ),
      (∀ a, ‖Φ (a + bT hn 0 (x' - x) (y' - y)) - Φ a‖ ≤ δ) →
      ‖(∫ z in m.𝓖, Φ (bT hn z x' y') * conj (chz ψ b₀ z) ∂m.lz) -
        ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ δ := by
    intro y y' x x' δ hδ
    have hpt : ∀ z : hermA D ρ, ‖Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
        Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ δ := by
      intro z
      have hs : bT hn z x' y' = bT hn z x y + bT hn 0 (x' - x) (y' - y) := by
        have h := bT_add hn z 0 x (x' - x) y (y' - y)
        have h1 : x + (x' - x) = x' := by abel
        have h2 : y + (y' - y) = y' := by abel
        rw [add_zero, h1, h2] at h
        exact h
      rw [← sub_mul, norm_mul, Complex.norm_conj, hnorm, mul_one, hs]
      exact hδ _
    rw [← integral_sub (hint x' y') (hint x y)]
    have h2 : ‖∫ z, (Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
        Φ (bT hn z x y) * conj (chz ψ b₀ z)) ∂(m.lz.restrict m.𝓖)‖ ≤
        δ * (m.lz.restrict m.𝓖 Set.univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
    rw [hrz, mul_one] at h2
    exact h2
  have hIB : ∀ (x : Mx D ρ p) (y : hermA D p),
      ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ B := by
    intro x y
    have h : ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤
        B * (m.lz.restrict m.𝓖 Set.univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hgb x y z)
    rwa [hrz, mul_one] at h
  have hIc : ∀ y : hermA D p,
      Continuous fun x : Mx D ρ p => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz := by
    intro y
    refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    have hv : Tendsto (fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y)) (𝓝 x₀) (𝓝 0) := by
      have hc : Continuous fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y) :=
        (continuous_bT hn).comp
          (continuous_const.prodMk ((continuous_id.sub continuous_const).prodMk continuous_const))
      simpa [hb0] using hc.tendsto x₀
    filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with x hx
    rw [dist_eq_norm]
    exact (hE y y x₀ x (ε / 2) fun a => (hx a).le).trans_lt (half_lt_self hε)
  have hin : ∀ y : hermA D p, Integrable
      (fun x => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) (m.μ.restrict m.𝓕) := fun y =>
    (integrable_const B).mono' (hIc y).aestronglyMeasurable (ae_of_all _ fun x => hIB x y)
  unfold pm
  refine continuous_iff_continuousAt.2 fun y₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hv : Tendsto (fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀)) (𝓝 y₀) (𝓝 0) := by
    have hc : Continuous fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀) :=
      (continuous_bT hn).comp
        (continuous_const.prodMk (continuous_const.prodMk (continuous_id.sub continuous_const)))
    simpa [hb0] using hc.tendsto y₀
  filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with y hy
  rw [dist_eq_norm, ← integral_sub (hin y) (hin y₀)]
  have hpt : ∀ x : Mx D ρ p, ‖(∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
      ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ ε / 2 := by
    intro x
    refine hE y₀ y x x (ε / 2) fun a => ?_
    rw [sub_self]
    exact (hy a).le
  have h2 : ‖∫ x, ((∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
      ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz) ∂(m.μ.restrict m.𝓕)‖ ≤
      ε / 2 * (m.μ.restrict m.𝓕 Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
  rw [hrμ, mul_one] at h2
  exact h2.trans_lt (half_lt_self hε)

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetUpperTriangularBlock
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.B3

variable {D : D7} {n : ℕ} {v : Pl D}

theorem det_upper_triangular_block {A : Type} [CommRing A] {n : ℕ} (a b d : Matrix (Fin n) (Fin n) A) : (blk4 a b 0 d).det = a.det * d.det := by
  rw [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_cT {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    (Formalism.UG.cT s M).det = s M.det := by
  rw [Formalism.UG.cT, Matrix.det_transpose]
  exact (RingHom.map_det s M).symm

theorem exists_det_parabolic {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = blk4 0 1 (-1) 0)
    (p : GlobalTheory.LocIntw.upperParabolic R σ Q) : ∃ d : R ⊗[F] E,
      (GlobalTheory.LocIntw.matR R σ p.1).det = (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d ∧
      sigR R σ (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d = 1 := by
  obtain ⟨a, b, c, d, e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR R σ p.1)
  obtain rfl : c = 0 := Matrix.ext fun i j => by
    have := GlobalTheory.LocIntw.lower_eq_zero p.2 i j
    rwa [e, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  have hu : Formalism.UG.cT (sigR R σ) (GlobalTheory.LocIntw.matR R σ p.1) * JR R Q * GlobalTheory.LocIntw.matR R σ p.1 = JR R Q := p.1.2
  rw [GlobalTheory.LocIntw.JR_eq R hQ, e, GlobalTheory.LocIntw.cT_blk4, GlobalTheory.LocIntw.cT_zero', StdUnn.Model.submatrix_fromBlocks_mul,
    StdUnn.Model.submatrix_fromBlocks_mul] at hu
  have hd : Formalism.UG.cT (sigR R σ) a * d = 1 := by simpa using (StdUnn.Model.blockMatrixTwoByTwoFin_injective hu).2.1
  have ha : (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) = a.det := by
    rw [GlobalTheory.LocIntw.coe_aUp, e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  refine ⟨d.det, ?_, ?_⟩
  · rw [ha, e, det_upper_triangular_block]
  · have h5 : (Formalism.UG.cT (sigR R σ) a * d).det = 1 := by rw [hd, Matrix.det_one]
    rw [Matrix.det_mul, det_cT] at h5
    rw [ha]
    exact h5

theorem eq_of_mul_eq_one {a b c : ℝ} (h1 : a * c = 1) (h2 : b * c = 1) : a = b := by
  have hc : c ≠ 0 := right_ne_zero_of_mul_eq_one h1
  exact mul_right_cancel₀ hc (h1.trans h2.symm)

abbrev PV (D : D7) (n : ℕ) (v : Pl D) : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) :=
  GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n)

abbrev aV (p : PV D n v) : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ :=
  GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) p

def lawV (χ : (AE D)ˣ →* Circle) (z : ℂ) (p : PV D n v) : ℂ :=
  (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow (absEv D.host.F D.host.E v (aV p)) (z + (n : ℂ) / 2)

theorem lawV_mul (χ : (AE D)ˣ →* Circle) (z : ℂ) (p q : PV D n v) :
    lawV χ z (p * q) = lawV χ z p * lawV χ z q := by
  simp only [lawV, aV, map_mul, Circle.coe_mul, npow_mul]
  ring

theorem law_emb {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (p : PV D n v) (g : G D n) :
    f (emb D.sp.cm.sig (Jst D n) v p * g) = lawV χ z p * f g := by
  have h := hf (GlobalTheory.LocIntw.embUp v p).1 (GlobalTheory.LocIntw.embUp v p).2
    (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) rfl g
  have e : Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) =
      ideleAt D.host.F D.host.E v (aV p) := GlobalTheory.LocIntw.aUp_embUp v p
  have e2 : absA D (ideleAt D.host.F D.host.E v (aV p)) = absEv D.host.F D.host.E v (aV p) := absE_ideleAt v _
  have e3 : (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)))) (z + (n : ℂ) / 2) =
      lawV χ z p :=
    (congrArg (fun y => (χ y : ℂ) * npow (absA D y) (z + (n : ℂ) / 2)) e).trans
      (congrArg (fun r => (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow r (z + (n : ℂ) / 2)) e2)
  exact h.trans (congrArg (· * f g) e3)

theorem shift {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f)
    (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) (g : G D n) (p₀ p₁ : PV D n v)
    {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v} (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀) {u : G D n} (hu : u ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (e₁ : k₀ * proj D.sp.cm.sig (Jst D n) v u = p₁ * k₁) : f (g * u) = lawV χ z p₁ * f g := by
  have embK : ∀ {k : GLoc D.sp.cm.sig (Jst D n) v}, k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v →
      emb D.sp.cm.sig (Jst D n) v k ∈ KAt D n v := fun hk =>
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  obtain ⟨uv, rfl⟩ : ∃ uv, emb D.sp.cm.sig (Jst D n) v uv = u := by
    rw [← range_emb] at hu; exact hu
  rw [proj_emb_self] at e₁
  obtain ⟨g', hg'⟩ : ∃ g' : G D n, g' = g * (emb D.sp.cm.sig (Jst D n) v (proj D.sp.cm.sig (Jst D n) v g))⁻¹ := ⟨_, rfl⟩
  have h1 : proj D.sp.cm.sig (Jst D n) v g' = 1 := by simp [hg']
  have h2 : g = g' * emb D.sp.cm.sig (Jst D n) v p₀ * emb D.sp.cm.sig (Jst D n) v k₀ := by
    rw [mul_assoc, ← map_mul, ← e₀, hg', inv_mul_cancel_right]
  have h3 : g * emb D.sp.cm.sig (Jst D n) v uv =
      g' * emb D.sp.cm.sig (Jst D n) v (p₀ * p₁) * emb D.sp.cm.sig (Jst D n) v k₁ := by
    rw [h2]
    simp only [mul_assoc, ← map_mul, e₁]
  have c : ∀ x : GLoc D.sp.cm.sig (Jst D n) v, g' * emb D.sp.cm.sig (Jst D n) v x = emb D.sp.cm.sig (Jst D n) v x * g' :=
    fun x => (commute_emb D.sp.cm.sig (Jst D n) x h1).symm.eq
  have h4 : f g = lawV χ z p₀ * f g' := by
    conv_lhs => rw [h2]
    rw [hK _ (embK hk₀), c, law_emb hf]
  rw [h3, hK _ (embK hk₁), c, show ((p₀ : GLoc D.sp.cm.sig (Jst D n) v) * p₁) = ((p₀ * p₁ : PV D n v) : GLoc D.sp.cm.sig (Jst D n) v) from rfl,
    law_emb hf, lawV_mul, h4]
  ring

def dV (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h : GLoc D.sp.cm.sig (Jst D n) v) : Fv D.host.F v :=
  splitProj τ (GlobalTheory.LocIntw.matR _ D.sp.cm.sig h).det

theorem dV_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h h' : GLoc D.sp.cm.sig (Jst D n) v) :
    dV τ (h * h') = dV τ h * dV τ h' := by
  rw [dV, dV, dV, GlobalTheory.LocIntw.matR_mul, Matrix.det_mul, map_mul]

theorem dV_one (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : dV τ (1 : GLoc D.sp.cm.sig (Jst D n) v) = 1 := by
  rw [dV, GlobalTheory.LocIntw.matR_one, Matrix.det_one, map_one]

theorem det_mem_subring {R : Type} [CommRing R] (S : Subring R) {m : ℕ} {M : Matrix (Fin m) (Fin m) R}
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun s _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem map_blk_eq_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (b : Matrix (Fin n) (Fin n) A)
    (h : ∀ i j, φ (b i j) = 0) : (blk4 1 b 0 1).map φ = 1 := by
  rw [GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    show b.map φ = 0 from Matrix.ext h, StdUnn.Model.block_matrix_one]

theorem norm_dV_of_mem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {k : GLoc D.sp.cm.sig (Jst D n) v}
    (hk : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) : ‖dV τ k‖ = 1 := by
  obtain ⟨h1, h2⟩ := mem_stabLoc_stdLattice_iff.1 hk
  have a1 : ‖dV τ k‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h1))
  have a2 : ‖dV τ k⁻¹‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h2))
  have e : dV τ k * dV τ k⁻¹ = 1 := by rw [← dV_mul, mul_inv_cancel, dV_one]
  have b1 : ‖dV τ k‖ ≤ 1 := by exact_mod_cast a1
  have b2 : ‖dV τ k⁻¹‖ ≤ 1 := by exact_mod_cast a2
  have e' : ‖dV τ k‖ * ‖dV τ k⁻¹‖ = 1 := by rw [← norm_mul, e, norm_one]
  refine le_antisymm b1 ?_
  calc (1 : ℝ) = ‖dV τ k‖ * ‖dV τ k⁻¹‖ := e'.symm
    _ ≤ ‖dV τ k‖ * 1 := mul_le_mul_of_nonneg_left b2 (norm_nonneg _)
    _ = ‖dV τ k‖ := mul_one _

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (C : Cut D n v) {x : hermA D n} (hx : x ∈ C.s) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  refine mem_atPts.2 ⟨mem_finPts_iff_forall.2 fun w => GlobalTheory.LocIntw.ext_matR ?_, fun u hu => GlobalTheory.LocIntw.ext_matR ?_⟩
  · refine (GlobalTheory.LocIntw.matR_mapH (evInf D.host.F w) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.inf x hx w i j
  · refine (GlobalTheory.LocIntw.matR_mapH (evFin D.host.F u) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.off x hx u (by simpa using hu) i j

theorem dV_nb (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) :
    dV τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = 1 := by
  have h : GlobalTheory.LocIntw.matR _ D.sp.cm.sig (proj D.sp.cm.sig (Jst D n) v (nb x)) = _ :=
    GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [dV, h, GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), det_upper_triangular_block, Matrix.det_one, mul_one, map_one]

theorem norm_split_eq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (p : PV D n v) (hp : ‖dV τ p.1‖ = 1) :
    ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ := by
  obtain ⟨d, h1, h2⟩ := exists_det_parabolic (GlobalTheory.LocIntw.Jst_eq D n) p
  have h3 : ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h1.symm).trans hp
  have h4 : ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [splitProj_comp, ← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h2).trans (by rw [map_one, norm_one])
  exact eq_of_mul_eq_one h3 h4

theorem chi_one {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    {k : G D n} (hk : k ∈ KAt D n v) (x : hermA D n) (p₁ : PV D n v)
    (e : k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x) = p₁ * k₁) :
    χ (ideleAt D.host.F D.host.E v (aV p₁)) = 1 := by
  refine hχ _ (norm_split_eq τ p₁ ?_)
  have hk' : proj D.sp.cm.sig (Jst D n) v k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v :=
    (GlobalTheory.LocIntw.mem_KUpAd.1 hk.1).1 v
  have h := congrArg (fun y => ‖dV τ y‖) e
  simp only [map_mul, dV_mul, dV_nb τ hnb, norm_mul, norm_one, norm_dV_of_mem τ hk₀, norm_dV_of_mem τ hk₁,
    norm_dV_of_mem τ hk', mul_one, one_mul] at h
  exact h.symm

end GlobalTheory.CompanionTheory.Jp.B3

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitaryStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_integral_of_unitary : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧ (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧ ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection | exact GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection | (intros; apply GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBoundStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_constant_term_bound : PcBound := by
  first | exact @GlobalTheory.CompanionTheory.PcB.pcBound | exact GlobalTheory.CompanionTheory.PcB.pcBound | (intros; apply GlobalTheory.CompanionTheory.PcB.pcBound <;> assumption)
end

