import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0004
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianPairingOntoInverseIdealAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeeSaw.HzOnto

open GlobalTheory.IwaPlace

variable {D : D7}

def pz (S : HSp D) (z x : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * z j

theorem pz_add (S : HSp D) (z x y : Fin S.rank → D.host.E) : pz S z (x + y) = pz S z x + pz S z y := by
  simp only [pz, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem pz_smul (S : HSp D) (z x : Fin S.rank → D.host.E) (c : D.host.E) :
    pz S z (c • x) = star c * pz S z x := by
  simp only [pz, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def valSub (S : HSp D) (M : Lat S) (z : Fin S.rank → D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {a | ∃ x ∈ M, pz S z x = a}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, M.add_mem hx hy, pz_add S z x y⟩
  zero_mem' := ⟨0, M.zero_mem, by simp [pz]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
    refine ⟨c' • x, M.smul_mem c' hx, ?_⟩
    have e : (c' • x : Fin S.rank → D.host.E) = (c' : D.host.E) • x := by
      funext i; exact (algebraMap_smul D.host.E c' (x i)).symm
    rw [e, pz_smul, hc', star_star, Algebra.smul_def]

theorem valSub_isFractional (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) :
    IsFractional (𝓞 D.host.E)⁰ (valSub S M z) := by
  have hsp : Submodule.span D.host.E (M : Set (Fin S.rank → D.host.E)) = ⊤ := hM.1.span_eq_top
  have hz : z ∈ Submodule.span D.host.E (M : Set (Fin S.rank → D.host.E)) := by rw [hsp]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (𝓞 D.host.E)⁰ D.host.E (M : Set _) z hz
  rw [Submodule.span_eq] at hd
  refine ⟨d, d.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb⟩ := (hM.2 _).1 hd x hx
  refine ⟨b, ?_⟩
  change (b : D.host.E) = (d : 𝓞 D.host.E) • pz S z x
  rw [hb, Algebra.smul_def]
  simp only [pz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : (d • z) j = algebraMap (𝓞 D.host.E) D.host.E d * z j := by
    change ((d : 𝓞 D.host.E) • z) j = _
    rw [Pi.smul_apply, Algebra.smul_def]
  rw [e]
  ring

def valIdl (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) : FI D :=
  ⟨valSub S M z, valSub_isFractional S M hM z⟩

theorem mem_valIdl {S : HSp D} {M : Lat S} {hM : IsSelfDualC S M} {z : Fin S.rank → D.host.E} {a : D.host.E} :
    a ∈ valIdl S M hM z ↔ ∃ x ∈ M, pz S z x = a := Iff.rfl

theorem hermAt_gen (S : HSp D) (z x : Fin S.rank → D.host.E) (α : Af D.host.F) :
    hermAt S (ratV z) (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] pz S z x := by
  simp only [hermAt, pz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (pairA D.host.F 0 α ⊗ₜ[D.host.F] star (1 * x i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram i j) *
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem hermAt_add (S : HSp D) (w x y : Fin S.rank → AE D) : hermAt S w (x + y) = hermAt S w x + hermAt S w y := by
  simp only [hermAt, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermAt_zero (S : HSp D) (w : Fin S.rank → AE D) : hermAt S w 0 = 0 := by
  simp [hermAt]

theorem hermAt_neg (S : HSp D) (w x : Fin S.rank → AE D) : hermAt S w (-x) = -hermAt S w x := by
  simp [hermAt, Finset.sum_neg_distrib]

theorem cA_sum_eq (S : HSp D) (Z y : Fin S.rank → AE D) :
    cA D (∑ l, (∑ m, cA D (Z m) * gA S m l) * y l) = hermAt S Z y := by
  have hg : ∀ m l, cA D (gA S m l) = gA S l m := fun m l => congrFun (congrFun (adj_gA S) l) m
  simp only [map_sum, map_mul, cA_cA, hermAt, Finset.sum_mul, hg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_not_intAt (v : Pl D) : ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := GlobalTheory.T.exists_adele_supportedAt_place_not_integral D v

theorem exists_not_mem_idV (v : Pl D) {𝔠 : FI D} (h : 𝔠 ≠ 0) : ∃ t ∈ idAt D (· = v), t ∉ idV 𝔠 v := by
  obtain ⟨x, hx, hg⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h
  obtain ⟨u, hu, hnu⟩ := exists_not_intAt (D := D) v
  have ht : incA D x * u ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hu
  refine ⟨incA D x * u, ht, fun hm => hnu ?_⟩
  have := ((hg _).1 hm).1
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hz_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ g ∈ idV 𝔠⁻¹ v, ∃ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) = g := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hL h𝔠 g hg
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hSD := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  set z := vecB o ζ with hzdef
  set 𝔦 : FI D := valIdl S M hM z with h𝔦def
  have hval : ∀ x ∈ latV S M (· = v), hermAt S (ratV z) x ∈ idV 𝔦 v := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, m, hm, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hermAt_gen]
      exact AddSubgroup.subset_closure ⟨α, hαi, hα, _, mem_valIdl.2 ⟨m, hm, rfl⟩, rfl⟩
    | zero => rw [hermAt_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hermAt_add]; exact add_mem hx hy
    | neg x _ hx => rw [hermAt_neg]; exact neg_mem hx
  have hkey : ∀ t ∈ idAt D (· = v),
      t ∈ idV 𝔠 v ↔ ∀ x ∈ latV S M (· = v), t * hermAt S (ratV z) x ∈ intAt D (· = v) := by
    intro t ht
    rw [← hL t ht, hSD.2.2 (t • ratV z) (fun i => Ideal.mul_mem_right _ _ ht)]
    simp only [GlobalTheory.IwaPlace.SDStable.hermAt_smul_left]
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h0
    obtain ⟨t, ht, htn⟩ := exists_not_mem_idV v h𝔠
    refine htn ((hkey t ht).2 fun x hx => ?_)
    have := hval x hx
    rw [h0, idV_zero, AddSubgroup.mem_bot] at this
    rw [this, mul_zero]
    exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  have hsub : ∀ a ∈ idV 𝔦⁻¹ v, a ∈ idV 𝔠 v := by
    intro a ha
    have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
    refine (hkey a haA).2 fun x hx => ?_
    have e := (h2 𝔦 1 h𝔦 one_ne_zero a haA).2 (by rwa [one_mul])
    exact (h1 _).1 (e _ (hval x hx))
  have hgA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ g hg
  have hg' : g ∈ idV 𝔦 v := by
    have e := (h2 𝔦⁻¹ 1 (inv_ne_zero h𝔦) one_ne_zero g hgA).1 fun a ha =>
      (h2 𝔠 1 h𝔠 one_ne_zero g hgA).2 (by rwa [one_mul]) a (hsub a ha)
    rwa [one_mul, inv_inv] at e
  have honto : ∀ b ∈ idV 𝔦 v, ∃ y ∈ latV S M (· = v), hermAt S (ratV z) y = b := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
      obtain ⟨m, hm, rfl⟩ := mem_valIdl.1 ha
      exact ⟨_, AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m, hm, rfl⟩, hermAt_gen S z m α⟩
    | zero => exact ⟨0, zero_mem _, hermAt_zero S _⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨y, hy, e⟩ := hb
      obtain ⟨y', hy', e'⟩ := hb'
      exact ⟨y + y', add_mem hy hy', by rw [hermAt_add, e, e']⟩
    | neg b _ hb =>
      obtain ⟨y, hy, e⟩ := hb
      exact ⟨-y, neg_mem hy, by rw [hermAt_neg, e]⟩
  obtain ⟨y, hy, e⟩ := honto g hg'
  exact ⟨y, hy, by rw [cA_sum_eq, e]⟩

end GlobalTheory.SeeSaw.HzOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn.Inhab

theorem weil_exists : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω := by
  intro D n V ψ hψ lam hlam χ hχ hr θ hθ μ 𝓕 hμ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) V 1 χ⁻¹ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ κ
  refine ⟨omS, ⟨?_, ?_, ?_⟩⟩
  · intro g a hg Φ x
    have := GlobalTheory.StdUnn.transport_levi D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
    rw [inv_inv] at this
    exact this
  · intro g b hg Φ x
    exact GlobalTheory.StdUnn.Unip.transport_unip D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
  · intro g hg Φ x
    exact GlobalTheory.StdUnn.WeylStd.main D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x

theorem fock_gauss (hg : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ))) : ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0 := by
  intro D n V θ l hl s hs U hUo hUc h0
  obtain ⟨f, hf⟩ := hg D n V l hl s hs
  set g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := U.indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    refine ⟨?_, ?_⟩
    · exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hUo).isLocallyConstant
    · exact HasCompactSupport.intro' hUc hUo.isClosed (fun x hx => Set.indicator_of_notMem hx _)
  have hmem : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hgSB, ?_⟩
    funext x
    rw [hf]
    rfl
  refine ⟨⟨_, hmem⟩, rfl, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hgSB, ?_⟩
    funext x
    simp [evalPoly]
  · show gauss V l s (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    have h1 : (fun τ => compAt θ τ (0 : Mx D V.rank n)) = fun _ => 0 := by
      funext τ; ext i j; simp [compAt]
    have h2 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 0 := by
      funext i j; simp
    rw [h1, h2, hgdef, Set.indicator_of_mem h0]
    simp [gauss]

theorem hyps_satisfiable :
    (∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H) ∧ (∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ → ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l) ∧ (∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω) ∧ (∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0) ∧ (∀ (D : D7) (m n : ℕ), ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧ (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U) :=
  ⟨GlobalTheory.StdUnn.exists_height, GlobalTheory.StdUnn.exists_realPar_of_isCharAF, weil_exists, fock_gauss GlobalTheory.GaussSchwartz.exists_schwartz_gauss, GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero⟩

end GlobalTheory.StdUnn.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevZeroInd in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntCoordsEv
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem alg_int_ev (c : D.host.F) : ∀ᶠ w in Filter.cofinite,
    algebraMap D.host.F (Fv D.host.F w) c ∈ (w : Pl D).adicCompletionIntegers D.host.F :=
  (algebraMap D.host.F (Af D.host.F) c).2

theorem repr_tmul_loc (w : Pl D) (x : Fv D.host.F w) (e : D.host.E) (i : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (x ⊗ₜ[D.host.F] e) i =
      x * algebraMap D.host.F (Fv D.host.F w) ((Module.finBasis D.host.F D.host.E).repr e i) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Finsupp.mapRange_apply, smul_eq_mul]

theorem int_coords_ev : ∀ᶠ w in Filter.cofinite, ∀ z ∈ intAE D, ∀ i,
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
      (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z) i ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
  classical
  set b := Module.finBasis D.host.F D.host.E
  set B := NumberField.RingOfIntegers.basis D.host.E
  have hev : ∀ᶠ w in Filter.cofinite, ∀ i j,
      algebraMap D.host.F (Fv D.host.F w) (b.repr ((B j : 𝓞 D.host.E) : D.host.E) i) ∈
        (w : Pl D).adicCompletionIntegers D.host.F := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact alg_int_ev _
  filter_upwards [hev] with w hw
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, o, rfl⟩ := hy
    intro i
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (α ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [hc, repr_tmul_loc]
    refine mul_mem (hα w) ?_
    have ho : (o : D.host.E) = ∑ j, (B.repr o j) • ((B j : 𝓞 D.host.E) : D.host.E) := by
      conv_lhs => rw [← B.sum_repr o]
      push_cast
      rfl
    rw [ho, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (hw i j) _
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [map_add, map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)
  | neg x _ hx => intro i; rw [map_neg, map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

end GlobalTheory.FinPlLoc

namespace GlobalTheory.FinPlLoc

open NumberField

variable {D : D7}

theorem sum_repr_tmul (w : Pl D) (y : Fv D.host.F w ⊗[D.host.F] D.host.E) :
    ∑ i, (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr y i ⊗ₜ[D.host.F]
      (Module.finBasis D.host.F D.host.E) i = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem glue : ∀ (D : D7) (a : Pl D → AE D), (∀ x, a x ∈ idAt D (· = x)) →
    (∃ T : Finset (Pl D), ∀ x ∉ T, a x ∈ intAt D (· = x)) →
    ∃ s : AE D, infPart D s = 0 ∧ ∀ x, s - a x ∈ idOff D (· = x) := by
  intro D a _ ⟨T, hT⟩
  classical
  set b := Module.finBasis D.host.F D.host.E
  let c : Fin (Module.finrank D.host.F D.host.E) → (w : Pl D) → Fv D.host.F w := fun i w =>
    (Algebra.TensorProduct.basis (Fv D.host.F w) b).repr (compAt D w (a w)) i
  have hc : ∀ i, ∀ᶠ w in Filter.cofinite, c i w ∈ (w : Pl D).adicCompletionIntegers D.host.F := by
    intro i
    filter_upwards [int_coords_ev (D := D), T.finite_toSet.compl_mem_cofinite] with w hw hwT
    exact hw _ (hT w hwT).2 i
  let C : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F := fun i => RestrictedProduct.mk (c i) (hc i)
  refine ⟨∑ i, pairA D.host.F 0 (C i) ⊗ₜ[D.host.F] b i, ?_, fun x => ?_⟩
  · rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => infPart_pair _ _
  · unfold idOff
    refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
    obtain ⟨w, rfl⟩ := w
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [compAt_pair]
    exact sum_repr_tmul w (compAt D w (a w))

end GlobalTheory.FinPlLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  first | exact @GlobalTheory.LineDual.line_pair_mem_idV | exact GlobalTheory.LineDual.line_pair_mem_idV | (intros; apply GlobalTheory.LineDual.line_pair_mem_idV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_groups_characters_family : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → VTie f v → ∀ t (n : ℕ) (G : Fin n → GLoc v) pl, GRead f G pl → ∀ i, (G i).Chars (f.t t) := by
  first | exact @GlobalTheory.TupChars.gLoc_chars | exact GlobalTheory.TupChars.gLoc_chars | (intros; apply GlobalTheory.TupChars.gLoc_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  first | exact @GlobalTheory.Corev.mem_latO_line_iff | exact GlobalTheory.Corev.mem_latO_line_iff | (intros; apply GlobalTheory.Corev.mem_latO_line_iff <;> assumption)
end

