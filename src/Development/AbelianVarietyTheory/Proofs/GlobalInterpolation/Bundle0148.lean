import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0147
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpec
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem usage₉ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl), Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) (GlobalTheory.PerQ.Co.bP I u a w c) ∧ (∀ x, iniH (N_m_succ B.R) (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) = ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧ (∀ x, (I.perIn u a).tz * (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) = x (Br.iL (N_m_succ B.R))) ∧ Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) (GlobalTheory.PerQ.Co.bM I u a w c) := by
  intro B X I _hI l u a w c
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  have hlat := (l.per u a).step.lsh_lat c.1 ((I.perIn u a).S'.rep c)
  have hP : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _)
      (GlobalTheory.PerQ.Co.bP I u a w c) := by
    obtain ⟨g, hg⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.places.resChar w) B.fields.E _ hlat.fg hlat.span_eq_top
    exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g) ⟨g, hg⟩
  refine ⟨hP, ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_localBasis_snoc_of_localBasis (N_m_succ B.R) (I.perIn u a).tz (l.per u a).tz_ne
    (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c))
    ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))
    (fun x => (l.per u a).Lsh_til c.1 ((I.perIn u a).S'.rep c) x) (B.places.resChar w) (GlobalTheory.PerQ.Co.bP I u a w c)
    (B.places.resChar_prime w) hP
  exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g) ⟨g, hg⟩

end GlobalTheory.PerQ.Co
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuples
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.PoissonSum

theorem countable_F (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem rat_add (ξ η : Fin N → F) : (rat (ξ + η) : Fin N → AF F) = rat ξ + rat η := by
  funext l; simp [rat]

theorem rat_neg (ξ : Fin N → F) : (rat (-ξ) : Fin N → AF F) = -rat ξ := by
  funext l; simp [rat]

theorem Bd_add_left (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.add_apply]; ring

theorem Bd_neg_right (a : Fin N → F) (u w : Fin N → AF F) :
    Bd (AF F) a u (-w) = -Bd (AF F) a u w := by
  simp only [Bd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply]; ring

theorem Bd_zero_left (a : Fin N → F) (w : Fin N → AF F) : Bd (AF F) a 0 w = 0 := by
  simp [Bd]

theorem Bd_rat (a : Fin N → F) (ξ η : Fin N → F) :
    Bd (AF F) a (rat ξ) (rat η) = algebraMap F (AF F) (Bd F a ξ η) := by
  simp [Bd, rat, map_sum, map_mul]

theorem continuous_Bd_right (a : Fin N → F) (w : Fin N → AF F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u w := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.PoissonSum

open GlobalTheory.SWQ.PoissonSum in
theorem GlobalTheory.SWQ.poisson_summation : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ
  haveI := countable_F F
  have hψ := hC.2.1
  obtain ⟨hHaar, hmem, hinj, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  haveI := hHaar
  obtain ⟨hint, hsum, hcont⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 Φ hΦ
  obtain ⟨-, hsumF, -⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 _ hFΦ
  set P : (Fin N → AF F) → ℂ := fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) with hP
  have hper : ∀ ξ u, P (rat ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => Φ (rat η + u)))
    simp [rat_add, add_assoc]
  have hcoef : ∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = Fo ψ ν a Φ (rat (-ξ)) := by
    intro ξ
    set G := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
    let e : (Fin N → F) ≃ G := Equiv.ofBijective (fun η => ⟨rat η, (hmem _).2 ⟨η, rfl⟩⟩)
      ⟨fun η η' h => hinj (congrArg Subtype.val h), fun γ => by
        obtain ⟨η, hη⟩ := (hmem γ.1).1 γ.2
        exact ⟨η, Subtype.ext hη.symm⟩⟩
    haveI : Countable G := e.surjective.countable
    set g : (Fin N → AF F) → ℂ := fun u => Φ u * ψ (-(Bd (AF F) a u (rat ξ))) with hg
    have hgc : Continuous g :=
      hΦ.1.mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)
    have hgn : ∀ u, ‖g u‖ = ‖Φ u‖ := fun u => by simp [hg, hψ.2.1]
    have hgi : Integrable g (muV N ν) :=
      (hint _ hHaar).norm.mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => (hgn u).le)
    have hshift : ∀ η u, g (rat η + u) = Φ (rat η + u) * ψ (-(Bd (AF F) a u (rat ξ))) := by
      intro η u
      simp only [hg, Bd_add_left, Bd_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]
    have hFo : Fo ψ ν a Φ (rat (-ξ)) = ∫ u, g u ∂(muV N ν) := by
      simp only [Fo, hg, rat_neg, Bd_neg_right]
    rw [hFo, hD.integral_eq_tsum'' g hgi, ← e.tsum_eq]
    have hvadd : ∀ η u, (e η +ᵥ u : Fin N → AF F) = rat η + u := fun η u => rfl
    simp_rw [hvadd, hshift]
    simp only [hP]
    simp_rw [← tsum_mul_right]
    refine integral_tsum (fun η => ?_) ?_
    · exact ((hΦ.1.comp (continuous_const.add continuous_id)).mul
        (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)).aestronglyMeasurable
    · have hl := hD.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)
      rw [← e.tsum_eq] at hl
      simp_rw [hvadd] at hl
      have hfin : ∫⁻ u, ‖Φ u‖ₑ ∂(muV N ν) ≠ ∞ := (hint _ hHaar).2.ne
      simp only [← ofReal_norm_eq_enorm] at hl ⊢
      simp only [norm_mul, hψ.2.1, mul_one]
      rw [← hl]
      simpa [ofReal_norm_eq_enorm] using hfin
  have hsc : Summable (fun ξ : Fin N → F => ‖Fo ψ ν a Φ (rat (-ξ))‖) := by
    have h := hsumF 0
    simp only [add_zero] at h
    exact (Equiv.neg (Fin N → F)).summable_iff.2 h
  have key := GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients F N ψ lam ν a hC D hD hD1 P _ hcont hper hcoef hsc 0
  have h0 : P 0 = th Φ := by simp [hP, th]
  rw [h0] at key
  rw [key, th]
  refine ((Equiv.neg (Fin N → F)).tsum_eq (fun ξ => Fo ψ ν a Φ (rat ξ))).symm.trans (tsum_congr fun ξ => ?_)
  simp [Bd_zero_left]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  first | exact @GlobalTheory.PerQ.trueWeights_built | exact GlobalTheory.PerQ.trueWeights_built | (intros; apply GlobalTheory.PerQ.trueWeights_built <;> assumption)
end

