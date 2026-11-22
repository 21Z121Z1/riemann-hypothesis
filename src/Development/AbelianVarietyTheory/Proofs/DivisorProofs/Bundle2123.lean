import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlocksEvaluation
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.ScaleBound

theorem exists_l2_const (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hPair : IsPair B M χX χW om r s r' s') (M₁ : Model σ X W) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n d) (hE : IsEv B M M₁ 1 1 ∅ e)
    (μ : @Measure (Fin n × Fin d → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl F, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  refine GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure ?_ (fun v => ?_) μ hμ
  · letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.schrodinger_intertwiner_l2_constant F (Fin n × Fin d) ψ hψ ei A hA
  · have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ :=
      GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA

variable {F : Type} [Field F] [NumberField F]

theorem tAd_eq_infScale (s : ℝ) : tAd F s = GlobalTheory.TorusTheta.infScale F s := by
  unfold tAd GlobalTheory.TorusTheta.infScale realAd
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (s - 1)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ s)
    rw [map_sub, map_sub, map_one, map_one, add_sub_cancel]
  · show (1 : FiniteAdeleRing (𝓞 F) F) + 0 = 1
    exact add_zero 1

variable (F) in

def scaleHom : ℝ →* AF F where
  toFun := GlobalTheory.TorusTheta.infScale F
  map_one' := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_one, map_one]
    rfl
  map_mul' u v := by
    unfold GlobalTheory.TorusTheta.infScale
    rw [map_mul, map_mul]
    exact Prod.ext rfl (one_mul (1 : FiniteAdeleRing (𝓞 F) F)).symm

theorem blkScale_eq {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (z : κ → AF F) :
    blkScale blk t z = fun j => GlobalTheory.TorusTheta.infScale F (∏ i, if j ∈ blk i then t i else 1) * z j := by
  funext j
  unfold blkScale
  congr 1
  show _ = scaleHom F _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact tAd_eq_infScale _
  · exact (map_one _).symm

theorem prod_scale_pow {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (t : Fin q → ℝ)
    (ht : ∀ i, 0 < t i) (f : ℕ) :
    ∏ j, (∏ i, if j ∈ blk i then t i else 1) ^ f = (∏ i, t i ^ (((f * (blk i).card : ℕ) : ℝ) / 2)) ^ 2 := by
  rw [Finset.prod_pow, Finset.prod_comm, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← Real.rpow_natCast (t i ^ _) 2,
    ← Real.rpow_mul (ht i).le, Nat.cast_ofNat, div_mul_cancel₀ _ two_ne_zero, Real.rpow_natCast, mul_comm, pow_mul]

theorem norm_scalar_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J) (c : ℂ), (∀ i, 0 < t i) → IsTorusU x y t a →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z)) →
      ‖c‖ ≤ ∏ i, t i ^ ex i := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y _ M₁ blk e hM₁ _ hE
  refine ⟨fun i => (((Module.finrank ℚ F * (blk i).card : ℕ) : ℝ) / 2), fun t a c ht _ hc => ?_⟩
  have hS := IsUWeilPair.isUSplitting hP.weil
  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE
  have heΦ := hE.maps Φ hΦ
  have hcont : Continuous (e Φ) := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) heΦ
  have hI0 : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ 0 := by
    intro h
    have hm : AEMeasurable (fun z => ‖e Φ z‖ₑ ^ 2) μ := (hcont.measurable.enorm.pow_const 2).aemeasurable
    rw [lintegral_eq_zero_iff' hm] at h
    have h' : e Φ =ᵐ[μ] 0 := h.mono fun z hz => by simpa using hz
    exact h0 ((hcont.ae_eq_iff_eq μ continuous_const).1 h')
  have hIt : ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (GlobalTheory.WeilM.schA_memLp_two F _ μ hμ _ heΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    simpa using h2.ne
  obtain ⟨l, hl⟩ := exists_l2_const F E σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE μ hμ
  have hU : ∫⁻ z, ‖e (om (a, 1) Φ) z‖ₑ ^ 2 ∂μ = ∫⁻ z, ‖e Φ z‖ₑ ^ 2 ∂μ := by
    rw [hl _ (hS.pres (a, 1) Φ hΦ), hl Φ hΦ, hS.unit μ hμ (a, 1) Φ hΦ]
  set u : Fin n × Fin d → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hu
  have hupos : ∀ j, 0 < u j := fun j => Finset.prod_pos fun i _ => by
    split_ifs
    · exact ht i
    · exact one_pos
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hupos μ hμ (fun z => ‖e Φ z‖ₑ ^ 2)
  simp only [hc Φ hΦ, enorm_mul, mul_pow, blkScale_eq] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hupos j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hsq := (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''
  rw [hu, prod_scale_pow blk t ht] at hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).le _) two_ne_zero).1 hsq).le

end GlobalTheory.ThKTorus.ScaleBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutationAtSmallPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perm_of_isDC {G : Type} [Group G] (J : Subgroup G) (x : G) (A : Finset G) (h : Bridge.IsDC J x A) (κ : G)
    (hκ : κ ∈ J) : ∃ σ : Equiv.Perm A, ∀ s : A, ((σ s : A) : G)⁻¹ * κ * s ∈ J := by
  classical
  have hex : ∀ s : A, ∃ a : A, (a : G)⁻¹ * (κ * s) ∈ J := by
    intro s
    obtain ⟨k₁, k₂, hs⟩ := h.1 s s.2
    obtain ⟨a, ⟨ha, haJ⟩, -⟩ := h.2 (κ * s) ⟨⟨κ, hκ⟩ * k₁, k₂, by rw [hs]; simp [mul_assoc]⟩
    exact ⟨⟨a, ha⟩, haJ⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [hss] at h1
    have h3 : (s : G)⁻¹ * s' ∈ J := by
      have := J.mul_mem (J.inv_mem h1) h2
      simpa [mul_assoc] using this
    obtain ⟨k₁, k₂, hs'⟩ := h.1 s' s'.2
    have hu := (h.2 s' ⟨k₁, k₂, hs'⟩).unique ⟨s.2, h3⟩ ⟨s'.2, by simp [J.one_mem]⟩
    exact Subtype.ext hu
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun s => ?_⟩
  simpa [mul_assoc] using hf s

theorem map_ev_eq_one_of_loc : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  obtain ⟨e, α, he, -, hs, hxα⟩ := hx
  obtain ⟨v, ε, ⟨a, rfl, -, ha⟩, hf, hv⟩ := GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨he, rfl⟩)
  have h0 : ev (a ⊗ₜ[D.host.F] 1) = 0 := by
    refine hev.2.2.1 a fun v' hv' => ha v' ?_
    rintro rfl
    apply hl
    rw [← hv] at hv'
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((l : ℕ) : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hv'
    rwa [map_natCast] at h1
  have h2 := GlobalTheory.SplitHeckeAdj.map_eq_one_of_supp (ev.comp (Formalism.L2.Theta.finPart D)) (e + Formalism.L2.Theta.cA D e)
    (by rw [hf]; exact h0) (Formalism.L2.Theta.mt V α) hs
  rw [hxα]
  exact h2

theorem chi_move {G : Type} [Group G] (J Lc : Subgroup G) (χ : J →* ℂˣ)
    (l2 : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l)
    (l3 : ∀ k : J, (k : G) ∈ Lc → χ k = 1) (κ κ' : J) (a s : G) (ha : a ∈ Lc) (hs : s ∈ Lc)
    (h : (κ' : G) = a⁻¹ * κ * s) : χ κ' = χ κ := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := l2 κ κ.2
  have e1 : κ = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : ((κ' * (⟨k₂, h₂⟩ : J)⁻¹ : J) : G) = a⁻¹ * k₁ * s := by
    show (κ' : G) * k₂⁻¹ = _
    rw [h, hk, mul_assoc a⁻¹, mul_assoc k₁, (hc s hs).eq]; group
  have e3 := l3 (κ' * (⟨k₂, h₂⟩ : J)⁻¹) (e2 ▸ Lc.mul_mem (Lc.mul_mem (Lc.inv_mem ha) hL) hs)
  rw [map_mul, map_inv, mul_inv_eq_one] at e3
  rw [e3, e1, map_mul, l3 ⟨k₁, h₁⟩ hL, one_mul]

set_option maxHeartbeats 1600000 in

theorem levChi_eq_of_loc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ∀ (κ κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i → s ∈ hkA p j t i → (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → levChi p j t κ' = levChi p j t κ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i h1 h2 κ κ' a s ha hs h
  have hb := p.charW.base
  have ha' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i a := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ a ha
  have hs' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i s := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ s hs
  refine hb.fam.tie.elim fun _ x => x.elim fun _ x => x.elim fun _ tie => ?_
  refine (hb.lev.βV j).elim fun c hc => ?_
  rw [one_pow] at hc
  refine ha'.elim fun e x => x.elim fun _ x => ?_
  have he := x.1
  have hsp := (tie.ok t _).1 (show (p.P.A3.A.ok t) × ℕ from i).1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc _ e he
    fun PP hP => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr)
  refine hl.elim fun Lc l => ?_
  have hA : a ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ ha' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  have hS : s ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ hs' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  exact chi_move _ Lc _ l.2.1 l.2.2.1 κ κ' a s hA hS h

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem chi_cancel {K R : Type} [Field K] [CommRing R] (io : K ≃+* ℂ) (emb : R →+* K) (hinj : Function.Injective emb)
    (u u' : Rˣ) (X X' : K) (hXX : X' = X) (hX : X ≠ 0) (c c' : ℂ) (hcc : c' = c) (hc : c ≠ 0)
    (e1 : io (emb u' * X') * c' = 1) (e2 : io (emb u * X) * c = 1) : u' = u := by
  subst hXX hcc
  have e4 := io.injective (mul_right_cancel₀ hc (e1.trans e2.symm))
  exact Units.ext (hinj (mul_right_cancel₀ hX e4))

theorem perm_core (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ)
    (hR : 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i), ∀ s : hkA p j t i, ((σ s : hkA p j t i) : Bridge.Gf (Vc D j))⁻¹ * κ * s ∈ levJ p j t := by
  have h : Bridge.IsDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) := (p.R.B.L j t).hecke.hDC i hR
  exact perm_of_isDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) h κ κ.2

theorem perm_gen (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (io : PadicAlgCl l ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ)
    (hev : ∀ τ, EvOk (incOf D e0 b τ) (ev τ)) (hkap : KapEq p j t ev bs rk kap) (hchi : ChiEq p j t io sh kap chi)
    (i : Ix p j t l N) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i.1), ∀ s : hkA p j t i.1, ∃ κ' : levJ p j t,
      (κ : Bridge.Gf (Vc D j)) * (s : Bridge.Gf (Vc D j)) = (σ s : Bridge.Gf (Vc D j)) * κ' ∧ kap κ' = kap κ ∧
        chi κ' = chi κ := by
  have hN : N = (Vc D j).rank := Fin.equiv_iff_eq.mp ⟨rk.toEquiv⟩
  have hR : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, by rw [← hN]; exact i.2.2.1⟩
  have hp := perm_core p j t i.1 hR κ
  refine hp.elim fun σ hσ => ?_
  have hinj : Function.Injective (intEmb Lf) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have loc : ∀ y ∈ hkA p j t i.1, ∀ τ,
      ((y : GL (Fin (Vc D j).rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) = 1 := by
    intro y hy τ
    have hy' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y := (p.R.B.L j t).hecke.hA_loc i.1 hR y hy
    exact map_ev_eq_one_of_loc (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y _ (ev τ) (hev τ) i.2.2.2 hy'
  have key : ∀ (κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i.1 → s ∈ hkA p j t i.1 →
      (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → kap κ' = kap κ ∧ chi κ' = chi κ := by
    intro κ' a s ha hs he
    have hmap : ∀ τ, (((κ' : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) =
        (((κ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) := by
      intro τ
      have ha1 := loc a ha τ
      have hs1 := loc s hs τ
      have ha' : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
        have h0 : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) *
            (((a : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
          rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.map_one _ (ev τ).map_zero (ev τ).map_one]
        rwa [ha1, mul_one] at h0
      rw [he]
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha', hs1, one_mul, mul_one]
    have hmat : ∀ τ, kapMat p j t ev bs rk κ' τ = kapMat p j t ev bs rk κ τ := by
      intro τ
      unfold kapMat matOf
      rw [hmap τ]
    have hK : kap κ' = kap κ := by
      funext τ
      apply Units.ext
      apply Matrix.ext
      intro a c
      apply hinj
      have h1 := (hkap κ' τ).trans ((hmat τ).trans (hkap κ τ).symm)
      exact congrFun (congrFun h1 a) c
    refine ⟨hK, ?_⟩
    have hL := levChi_eq_of_loc p j t i.1 hR.1 hR.2 κ κ' a s ha hs he
    have hX : (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ?_
      exact ((Matrix.GeneralLinearGroup.det (kap κ τ)).isUnit.map (intEmb Lf)).ne_zero
    have hXX : (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) = ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ :=
      congrArg (fun f : D.what₂.Tau → GL (Fin N) (intR Lf) => ∏ τ, intEmb Lf (f τ).val.det ^ sh τ) hK
    have hcc : ((levChi p j t κ' : ℂˣ) : ℂ) = ((levChi p j t κ : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hL
    have e1 : io (intEmb Lf (chi κ') * ∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) * ((levChi p j t κ' : ℂˣ) : ℂ) = 1 :=
      hchi κ'
    have e2 : io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1 :=
      hchi κ
    exact chi_cancel io (intEmb Lf) hinj (chi κ) (chi κ') (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ)
      (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) hXX hX ((levChi p j t κ : ℂˣ) : ℂ) ((levChi p j t κ' : ℂˣ) : ℂ) hcc
      (levChi p j t κ).ne_zero e1 e2
  refine ⟨σ, fun s => ⟨⟨((σ s : hkA p j t i.1) : Bridge.Gf (Vc D j))⁻¹ * κ * s, hσ s⟩, ?_, ?_, ?_⟩⟩
  · show (κ : Bridge.Gf (Vc D j)) * s = (σ s : Bridge.Gf (Vc D j)) * ((σ s : Bridge.Gf (Vc D j))⁻¹ * κ * s)
    group
  · exact (key _ _ _ (σ s).2 s.2 rfl).1
  · exact (key _ _ _ (σ s).2 s.2 rfl).2

set_option maxHeartbeats 800000 in
open Classical in

theorem permAt (p : PtAt ex Csz) (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    PermAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hC
  obtain ⟨-, -, -, hev, hkap, hchi⟩ := hC
  dsimp only [GlobalTheory.FrameOf.frameOf]
  intro i κ
  exact perm_gen p j (p.R.mu w) e0 b io ev bs rk sh Lf kap chi hev hkap hchi i κ

end Point

theorem permSt : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold InRange AtPts
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩

end GlobalTheory.FramePerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgreeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_maps_two_triples_agree : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @GlobalTheory.RealMapsChars.isRealMaps_of_sameExp | exact GlobalTheory.RealMapsChars.isRealMaps_of_sameExp | (intros; apply GlobalTheory.RealMapsChars.isRealMaps_of_sameExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueMatrixDatum_fourierExpansion_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  first | exact @GlobalTheory.ResidueFourier.omegaQ_fourier | exact GlobalTheory.ResidueFourier.omegaQ_fourier | (intros; apply GlobalTheory.ResidueFourier.omegaQ_fourier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
section
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullbackStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarDilationElement_support_det_pullback : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  first | exact @GlobalTheory.DilScalar.scalar_dil_facts | exact GlobalTheory.DilScalar.scalar_dil_facts | (intros; apply GlobalTheory.DilScalar.scalar_dil_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReductionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  first | exact @GlobalTheory.CapelliLink.linkage | exact GlobalTheory.CapelliLink.linkage | (intros; apply GlobalTheory.CapelliLink.linkage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at_holds : GlobalTheory.BigTop.Fun.SizeAt := by
  first | exact @GlobalTheory.BigTop.Fun.SizeProof.sizeAt | exact GlobalTheory.BigTop.Fun.SizeProof.sizeAt | (intros; apply GlobalTheory.BigTop.Fun.SizeProof.sizeAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatementStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SmallStatement : SmallSt := by
  first | exact @GlobalTheory.ExpTie.smallSt | exact GlobalTheory.ExpTie.smallSt | (intros; apply GlobalTheory.ExpTie.smallSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeakStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  first | exact @GlobalTheory.BigOn.splitPartRealisationWithScalars_char_of_weak | exact GlobalTheory.BigOn.splitPartRealisationWithScalars_char_of_weak | (intros; apply GlobalTheory.BigOn.splitPartRealisationWithScalars_char_of_weak <;> assumption)
end

