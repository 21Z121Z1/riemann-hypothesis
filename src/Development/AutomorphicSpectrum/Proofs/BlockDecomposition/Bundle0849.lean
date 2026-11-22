import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0846
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0844
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0843
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0837
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0836
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0839
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Bundle0003
import GroundTheory.AutomorphicForms.Bundle0005
import GroundTheory.AutomorphicForms.CompactSelfAdjoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0847
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0845
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCutoffContinuousCompactSupportStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_cutoff_continuous_compact_support : ∀ (F : Type) [Field F] [NumberField F] (G : Ainf F → ℝ) (a : (AF F)ˣ), Continuous G → HasCompactSupport G →
    Continuous (phiA G a) ∧ HasCompactSupport (phiA G a) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.phiA_test | exact GlobalTheory.CompanionTheory.BasePsi.phiA_test | (intros; apply GlobalTheory.CompanionTheory.BasePsi.phiA_test <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ConjSat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem locU_eq_of_under {w u : HeightOneSpectrum (𝓞 E)}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : locU n u = locU n w := by
  simp only [locU, h]

abbrev flipGL (w : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E) ≃* GL (Fin n) (w.adicCompletion E) :=
  GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n

theorem flipGL_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)) :
    flipGL w g = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem continuous_flipGL (w : HeightOneSpectrum (𝓞 E)) : Continuous (flipGL (n := n) w) := by
  have : (flipGL (n := n) w : _ → _) = fun g => GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
    funext (flipGL_eq w)
  rw [this]
  exact (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem cLoc_eq_flipGL (x : UA E n) (w : HeightOneSpectrum (𝓞 E)) :
    cLoc w x = flipGL w (cLoc (GlobalTheory.ThetaSatake.cw w) x) :=
  (GlobalTheory.BCT.LocCpt.cLoc_eq_invT x w).trans (flipGL_eq w _).symm

def flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) : SmIrr (GLw n (GlobalTheory.ThetaSatake.cw w)) where
  V := σ.V
  ρ := σ.ρ.comp (flipGL w).toMonoidHom
  smooth v := (σ.smooth v).preimage (continuous_flipGL w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (flipGL w).surjective σ.irred

theorem hasSatGL_flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) {B : Multiset ℂˣ}
    (h : HasSatGL w σ.ρ B) : HasSatGL (GlobalTheory.ThetaSatake.cw w) (flipIrr σ).ρ (B.map (·⁻¹)) := by
  refine GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w).symm (fun a => ?_)
    (GlobalTheory.ThetaSatake.absNorm_cw w) (LinearEquiv.refl ℂ σ.V) (fun g x => ?_) h
  · have := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w).2.2 ((GlobalTheory.ThetaSatake.cloc w).symm a)
    exact (this.symm.trans (congrArg _ ((GlobalTheory.ThetaSatake.cloc w).apply_symm_apply a)))
  · change σ.ρ (flipGL w ((flipGL w).symm g)) x = σ.ρ g x
    rw [MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.ConjSat

open GlobalTheory.CompanionTheory.ConjSat in

theorem GlobalTheory.CompanionTheory.ConjSat.satConj : PositivityTheory.Rg.BcB.F.RS.SatConj := by
  intro E _ _ _ n π w u B _ _ hc ⟨σ, ⟨hirr, f, f0, hf, hfx⟩, hB⟩
  obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
  refine ⟨flipIrr σ, ⟨(flipIrr σ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr σ hB⟩
  have hx : (x : UA E n) ∈ locU n w := locU_eq_of_under hc.1 ▸ x.2
  have := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at this
  change f (σ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact this

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf
open GlobalTheory.Eis

variable {D : D7} {n ρ p : ℕ}

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  simp only [chz, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', AddChar.map_add_eq_mul]

theorem chz_norm {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a : hermA D ρ) :
    ‖chz ψ b₀ a‖ = 1 := hψ.2.1 _

theorem chz_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) : Continuous (chz ψ b₀) :=
  GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (b₀.1.map (incA D) : Mx D ρ ρ)

theorem chz_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (l : ratHerm D ρ) :
    chz ψ b₀ l.1 = 1 :=
  GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (b₀.1.map (incA D) : Mx D ρ ρ)) ⟨b₀.1, rfl⟩ l

theorem continuous_jacobi_map_zero {hn : ρ + p = n} (M : Maps D hn) : Continuous fun z : hermA D ρ => M.nzx z 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)

set_option maxHeartbeats 1600000 in

theorem unfold_on {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {b₀ : HermE D ρ} (hb₀ : b₀.1.det ≠ 0) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {s : ℂ} {f : G D n → ℂ}
    (hf : Continuous f) (hl : IsLaw χ s f) (hs : (n : ℝ) / 2 < s.re) (C : Set (G D n)) (hC : IsCompact C) :
    ∃ Um : Cosets (P D n) (GF D n) → ℝ, Summable Um ∧
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧ ∀ g ∈ C,
      (∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ ∑' l : ratHerm D ρ, Um (e (l, u))) ∧
      HasSum (fun u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E =>
        Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)) (zc M m ψ b₀ (eisS f) g) := by
  obtain ⟨hinv, hdet, hmaj⟩ := GlobalTheory.T.eisenstein_terms_uniformly_summable hχ hf hl hs
  obtain ⟨hHaar, hFD, hvol⟩ := m.hz
  obtain ⟨hadd, hcsh, hcem, hrat⟩ := GlobalTheory.T.heisenberg_centre_rational_form M
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := ρ)
  haveI : Countable (ratHerm D ρ) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  haveI : Countable (Cosets (P D p) (GF D p)) := countable_cosets
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) := countable_mat ρ p
  obtain ⟨e, he, hfib, hτe, hterm⟩ := GlobalTheory.T.heisenberg_cosets_param_rational hn M
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  have hcn := continuous_jacobi_map_zero M
  obtain ⟨Um, hUm, hub⟩ := hmaj ((fun d : hermA D ρ × G D n => M.nzx d.1 0 * d.2) '' (K0 ×ˢ C))
    ((hK0.prod hC).image ((hcn.comp continuous_fst).mul continuous_snd))
  refine ⟨Um, hUm, e, he, fun g hg => ?_⟩
  let F : Cosets (P D n) (GF D n) → hermA D ρ → ℂ := fun q b => term (P D n) (GF D n) f (M.nzx b 0 * g) q
  let F0 : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → hermA D ρ → ℂ := fun u z =>
    f (M.w * M.nzx z 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g))
  let ch : hermA D ρ → ℂ := fun b => conj (chz ψ b₀ b)
  let τ : ratHerm D ρ → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l =>
    rmulEquiv _ _ ⟨M.nzx l.1 0, (hrat l).1⟩
  have hτ : ∀ (l : ratHerm D ρ) q b, F q ((l : hermA D ρ) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [hadd, mul_assoc]
    exact term_mul_left hinv ⟨M.nzx l.1 0, (hrat l).1⟩ _ q
  have hchc : Continuous ch := Complex.continuous_conj.comp (chz_cont hψ b₀)
  have hF : ∀ q, Continuous (F q) := fun q =>
    hf.comp (continuous_const.mul (hcn.mul continuous_const))
  have hF0 : ∀ (l : ratHerm D ρ) u b, F (e (l, u)) b = F0 u ((l : hermA D ρ) + b) := fun l u b => by
    simp only [F, F0]
    rw [hterm f hinv, hadd]
    congr 1
    have h1 : M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * (M.nzx b 0 * g) =
        M.nzx b 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g) := by
      rw [← mul_assoc, mul_assoc (M.sh _), ← hcem, ← mul_assoc, ← hcsh]
      simp only [mul_assoc]
    simp only [mul_assoc] at h1 ⊢
    rw [h1]
  have key := GlobalTheory.T.fundamental_domain_unfolding_two_sums m.lz (ratHerm D ρ) m.𝓖 hFD hvol
    (fun q : Cosets (P D n) (GF D n) => zKer hn (ratOf q.out)) (⊥ : Submodule D.host.E (Fin ρ → D.host.E)) F F0 ch
    (fun q => (hF q).aestronglyMeasurable) hchc.aestronglyMeasurable
    (fun b => by simp only [ch, RCLike.norm_conj]; exact chz_norm hψ b₀ b)
    (fun a b => by simp only [ch]; rw [chz_add, map_mul])
    (fun l => by simp only [ch]; rw [chz_rat hψ b₀ l, map_one])
    Um hUm τ hτ
    (fun l q => by
      obtain ⟨ζ, -, hζ⟩ := (hrat l).2
      have := GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv (D := D) (n := n) q ⟨M.nzx l.1 0, (hrat l).1⟩ (bl hn ζ 0 0 0) hζ
      change (cosetCell (τ l q)).comap (zinc hn) = (cosetCell q).comap (zinc hn)
      rw [show cosetCell (τ l q) = cosetCell q from this])
    (fun b => by
      obtain ⟨γ, hγ, hb⟩ := hKc b
      refine ⟨-⟨γ, hγ⟩, fun q => ?_⟩
      have h1 := hτ (-⟨γ, hγ⟩) q (γ + b)
      have h2 : (((-⟨γ, hγ⟩ : ratHerm D ρ) : hermA D ρ) + (γ + b)) = b := by simp
      rw [h2] at h1
      rw [h1]
      exact hub _ _ ⟨(γ + b, g), ⟨hb, hg⟩, rfl⟩)
    e he hfib (fun l l' u => hτe l l' u (hrat l').1) hF0
    (fun y hy => by
      obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.nondegenerate_centre_character_cell hn hψ b₀ hb₀ y hy
      refine ⟨ν, ?_, fun q hq b => ?_⟩
      · intro h
        apply hν1
        have := congrArg (starRingEnd ℂ) h
        simpa [ch] using this
      · obtain ⟨x, hxP, a, ha, hd, hpe⟩ : ∃ x ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat x) = a.1 ∧
            Matrix.GeneralLinearGroup.det a = 1 ∧ (q.out : G D n) * M.nzx ν 0 = x * (q.out : G D n) := by
          obtain ⟨x, hx, a, ha, hd, hpe⟩ := hν (q.out : GF D n) (M.nzx ν 0) (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq
            (by rw [M.nzx_mat, adj_zero])
          exact ⟨x, hx, a, ha, hd, hpe⟩
        simp only [F, term]
        rw [hadd, mul_assoc (M.nzx ν 0), ← mul_assoc _ (M.nzx ν 0), hpe, mul_assoc, hdet x hxP a ha hd])
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨hi, hle⟩ := key.1 u
    refine le_trans ?_ hle
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [F0, norm_mul, RCLike.norm_conj, chz_norm hψ b₀, mul_one]
  · exact key.2

theorem zUnfold : ZUnfold := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ χ hχ s f hf hl hs g
  refine ⟨?_, fun C hC => ?_⟩
  · obtain ⟨Um, -, e, -, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs {g} isCompact_singleton
    exact (h g rfl).2
  · obtain ⟨Um, hUm, e, he, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs C hC
    refine ⟨fun u => ∑' l : ratHerm D ρ, Um (e (l, u)), ?_, fun g hg u => (h g hg).1 u⟩
    have h1 : Summable (fun x : (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) × ratHerm D ρ => Um (e (x.2, x.1))) :=
      hUm.comp_injective (he.comp Prod.swap_injective)
    exact h1.prod

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresentedStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModuleStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_module_eq_norm_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgHeA

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_smul_rep {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (b : H) :
    Integrable (fun g => f g • τ g b) ν := by
  refine (hf.norm.mul_const ‖b‖).mono' (hf.aestronglyMeasurable.smul (hτ.4 b).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_smul, hτ.norm]

theorem integrable_mul_inner {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (a b : H) :
    Integrable (fun g => f g * ⟪a, τ g b⟫_ℂ) ν := by
  refine (hf.norm.mul_const (‖a‖ * ‖b‖)).mono'
    (hf.aestronglyMeasurable.mul (continuous_const.inner (hτ.4 b)).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖⟪a, τ g b⟫_ℂ‖ ≤ ‖a‖ * ‖τ g b‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [hτ.norm]

def coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ g, f g • τ g b ∂ν
      map_add' := fun x y => by
        rw [← integral_add (integrable_smul_rep hτ hf x) (integrable_smul_rep hτ hf y)]
        simp only [map_add, smul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        simp only [map_smul, smul_comm c] }
    (∫ g, ‖f g‖ ∂ν) fun b => by
      refine (norm_integral_le_of_norm_le (hf.norm.mul_const ‖b‖) (.of_forall fun g => ?_)).trans_eq ?_
      · rw [norm_smul, hτ.norm]
      · rw [integral_mul_const]

theorem coefOp_apply (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (b : H) :
    coefOp ν τ hτ f hf b = ∫ g, f g • τ g b ∂ν := rfl

theorem inner_coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (a b : H) :
    ⟪a, coefOp ν τ hτ f hf b⟫_ℂ = ∫ g, f g * ⟪a, τ g b⟫_ℂ ∂ν := by
  rw [coefOp_apply, ← integral_inner (integrable_smul_rep hτ hf b)]
  simp only [inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionThetaSeriesInvarianceStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_function_theta_series_invariance : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.finite_contributing | exact GlobalTheory.CompanionTheory.BasePsi.finite_contributing | (intros; apply GlobalTheory.CompanionTheory.BasePsi.finite_contributing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionTranslateRayUnitsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_function_translate_ray_units : ∀ (F : Type) [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ (δ : ℝ), 0 < δ → ∀ t : Fˣ,
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (a * r δ)) =
      if ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (phiA G a (fun _ => θ δ * algebraMap F (Ainf F) (t : F)) *
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.pure_term | exact GlobalTheory.CompanionTheory.BasePsi.pure_term | (intros; apply GlobalTheory.CompanionTheory.BasePsi.pure_term <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_integral_ray_formula : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_integral_ray_limit : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → (∀ᶠ ε : ℝ in 𝓝[>] 0, Th φ A (y * ofF (r ε)) ≠ ⊤) → Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (y * ofF (r ε))) (𝓝[>] 0) (𝓝 ((ENNReal.ofReal (md n))⁻¹ * vol b li lam S φ A)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegralStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_extension_fibre_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.compact_finite_block <;> assumption)
end

