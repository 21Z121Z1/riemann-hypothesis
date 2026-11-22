import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0027
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0017
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0024
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLawOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocD
section
noncomputable section

set_option linter.style.haveILetI false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem uni_blocks (σ : R →+* R) (h : Matrix (Fin (n + n)) (Fin (n + n)) R) (hu : Uni σ h) :
    Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁ - Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = 1 ∧
      Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂ = Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ := by
  have e := congrArg bf hu
  unfold J2 at e
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, ← fromBlocks_toBlocks (bf h), cT_fromBlocks, fromBlocks_multiply,
    fromBlocks_multiply] at e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at e
  obtain ⟨-, -, e3, e4⟩ := fromBlocks_inj.1 e
  refine ⟨?_, ?_⟩
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = -1 := e3
    rw [← neg_neg (1 : Matrix (Fin n) (Fin n) R), ← this]; abel
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ = 0 := e4
    rw [neg_add_eq_zero] at this; exact this

theorem schur {K : Type} [CommRing K] (P Q A B C D : Matrix (Fin n) (Fin n) K) (h1 : P * A - Q * C = 1) (h2 : P * B = Q * D)
    (hD : IsUnit D.det) : IsUnit P.det := by
  have hQ : Q = P * B * D⁻¹ := by rw [h2, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
  have : P * (A - B * D⁻¹ * C) = 1 := by
    rw [← h1, hQ]; simp only [Matrix.mul_sub, Matrix.mul_assoc]
  have hd := congrArg Matrix.det this
  rw [det_mul, det_one] at hd
  exact ⟨⟨_, _, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

theorem lift2 (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] (hne : 𝔪.comap σ ≠ 𝔪)
    (s t : R ⧸ 𝔪) : ∃ x : R, Ideal.Quotient.mk 𝔪 x = s ∧ Ideal.Quotient.mk 𝔪 (σ x) = t := by
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have h' : (𝔪.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hsup : 𝔪 ⊔ 𝔪.comap σ = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h' (Ne.symm hne)
  have h1 : (1 : R) ∈ 𝔪 ⊔ 𝔪.comap σ := hsup ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hf' : σ f ∈ 𝔪 := hf
  have he0 : Ideal.Quotient.mk 𝔪 e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 he
  have hf1 : Ideal.Quotient.mk 𝔪 f = 1 := by
    rw [show f = 1 - e by rw [← hef]; ring, map_sub, map_one, he0, sub_zero]
  have hsf : Ideal.Quotient.mk 𝔪 (σ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf'
  have hse : Ideal.Quotient.mk 𝔪 (σ e) = 1 := by
    rw [show e = 1 - f by rw [← hef]; ring, map_sub, map_one, map_sub, map_one, hsf, sub_zero]
  refine ⟨u * f + σ y * e, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, hf1, he0]; ring
  · rw [map_add, map_mul, map_mul, map_add, map_mul, map_mul, hσ, hsf, hse]; ring

theorem caseB (hS : LocRedSplit) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hne : 𝔪.comap σ ≠ 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  obtain ⟨ab, db, I, hI⟩ := hS (R ⧸ 𝔪) n (Matrix.nonsingInvUnit _ hdet)
  choose x hx using fun i j => lift2 σ hσ 𝔪 hne ((ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) i j)
    (((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) j i)
  let a : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => x i j
  have ha1 : a.map (Ideal.Quotient.mk 𝔪) = ab := by ext i j; exact (hx i j).1
  have ha2 : (Formalism.UG.cT σ a).map (Ideal.Quotient.mk 𝔪) = ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    ext i j; exact (hx j i).2
  have hab : IsUnit (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units ab
  have hdb : IsUnit ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units _
  have hadet : IsUnit a.det := by
    refine isUnit_of σ 𝔪 horb _ ?_ ?_
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [det_map, ha1] at h0
      exact hab.ne_zero h0
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [← det_cT, det_map, ha2] at h0
      exact hdb.ne_zero h0
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact hadet.map σ
  have hinv : ((Formalism.UG.cT σ a)⁻¹).map (Ideal.Quotient.mk 𝔪) = (db : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    rw [map_nonsing_inv _ _ hca, ha2, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units db)]
  set h := g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I with hh
  have hmap : h.map (Ideal.Quotient.mk 𝔪) =
      g.map (Ideal.Quotient.mk 𝔪) * GlobalTheory.StdUnn.blk4 (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) 0 0 db * wIm I := by
    rw [hh, Matrix.map_mul, Matrix.map_mul, block_matrix_map, ha1, hinv, wIm_map, Matrix.map_zero _ (map_zero _)]
  have hδ : IsUnit ((blkDm h).map (Ideal.Quotient.mk 𝔪)).det := by rw [blkDm_map, hmap]; exact hI
  refine ⟨a, I, hadet, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map] at h0
    exact hδ.ne_zero h0
  · have hu : Uni σ h := (hg.mul (uni_levi σ hσ a hadet)).mul (uni_wIm σ I)
    obtain ⟨e1, e2⟩ := uni_blocks σ h hu
    have hπσ : ∀ y : Matrix (Fin n) (Fin n) R, (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) =
        (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) := fun _ => rfl
    have e1' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e1
    have e2' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e2
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e1' e2'
    have hD : IsUnit ((bf h).toBlocks₂₂.map (Ideal.Quotient.mk 𝔪)).det := hδ
    have hP := schur _ _ _ _ _ _ e1' e2' hD
    intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [blkDm_eq, ← det_cT, det_map] at h0
    exact hP.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableAbsThetaToReal
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ}

def thS (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ℂ := ∑' ξ, f (invPt V h ξ)

theorem leftInv_thS (V : HSp D) (f : Mx D V.rank n → ℂ) : LeftInv (GQ V) (thS V f) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (invPt V h ξ))
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem enorm_thS_le (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ‖thS V f h‖ₑ ≤ absTheta V f h :=
  enorm_tsum_le_tsum_enorm

theorem absTheta_mono (V : HSp D) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) (h : GA D V) :
    absTheta V f h ≤ absTheta V M h :=
  ENNReal.tsum_le_tsum fun _ => enorm_le_iff_norm_le.2 (hfM _)

theorem absThetaInt_mono (V : HSp D) (ν : Measure (GA D V)) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) :
    absThetaInt V ν f ≤ absThetaInt V ν M :=
  lintegral_mono fun q => absTheta_mono V hfM _

theorem absThetaInt_smul_lt (V : HSp D) (ν : Measure (GA D V)) (c : ℂ) {M : Mx D V.rank n → ℂ}
    (hM : absThetaInt V ν M < ⊤) : absThetaInt V ν (c • M) < ⊤ := by
  unfold absThetaInt
  have : ∀ q, descend (GQ V) (absTheta V (c • M)) q = ‖c‖ₑ * descend (GQ V) (absTheta V M) q := fun q =>
    GlobalTheory.AbsThetaSemi.absTheta_smul V c M q.out
  simp_rw [this]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top hM

theorem aestronglyMeasurable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : AEStronglyMeasurable (descend (GQ V) (thS V f)) (autMeasure V ν) := by
  rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_thS V f).lift_descend]
  have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V f) q < ⊤ :=
    ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hf) hfin.ne
  have hae' : ∀ᵐ h ∂ν, absTheta V f h < ⊤ := by
    have := (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)).ae hae
    filter_upwards [this] with h hh
    rwa [(leftInv_absTheta V f).descend_mk] at hh
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => f (invPt V h ξ) :=
    hae'.mono fun h hh => Summable.of_enorm hh.ne
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν)
    (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
    (f := fun F h => ∑ ξ ∈ F, f (invPt V h ξ))
    (fun F => (continuous_finsetSum F fun ξ _ =>
      hf.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
    (hsum.mono fun h hh => hh.hasSum)

theorem integrable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : Integrable (descend (GQ V) (thS V f)) (autMeasure V ν) :=
  ⟨aestronglyMeasurable_thS V ν hf hfin,
    lt_of_le_of_lt (lintegral_mono fun q => enorm_thS_le V f q.out) hfin⟩

theorem ae_absTheta_lt (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V M) q < ⊤ :=
  ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM) hfin.ne

theorem integrable_absTheta_toReal (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) :
    Integrable (fun q => (descend (GQ V) (absTheta V M) q).toReal) (autMeasure V ν) :=
  integrable_toReal_of_lintegral_ne_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM).aemeasurable hfin.ne

theorem sch_facts (hP : GlobalTheory.Published.WeilThetaConvergence) (V : HSp D) (hn : 1 ≤ n) (hr : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {M : Mx D V.rank n → ℂ}
    (hM : M ∈ schwartzA θ V.rank n) : Continuous M ∧ absThetaInt V ν M < ⊤ :=
  ⟨(GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ M (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ M hM)).1,
    hP D n V hn (Or.inr hr) θ hθ ν hν ⟨M, hM⟩⟩

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LawNbarA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.NbarH

variable {m n : ℕ}

theorem ftLoc_const_mul (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s (fun v => k * g v) u = k * ftLoc ε s g u := by
  unfold ftLoc
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul k _

theorem ftLoc_const_mul' (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    ftLoc ε s (fun v => k * g v) = fun u => k * ftLoc ε s g u := funext fun u => ftLoc_const_mul ε s k g u

theorem sigR_sq (ε : Fin m → Bool) (a : Fin m) : (VacC.sigR ε a : ℂ) ^ 2 = 1 := by
  unfold VacC.sigR; split_ifs <;> norm_num

theorem ftLoc_vac (ε : Fin m → Bool) (t c s : ℝ) (hc : 0 < c) (hs : s ^ 2 = c ^ 2) :
    ftLoc ε s (vac ε t c) = fun u => ((Real.pi : ℂ) / c) ^ (m * n) * vac (n := n) ε t c u := by
  funext u
  have hs' : (s : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [VacC.ftLoc_eq, VacC.vac_eq, VacS.ftG_DG _ _ _ _ (fun a j => by simpa using hc)]
  have hγ : (fun (a : Fin m) (j : Fin n) => (s : ℂ) ^ 2 * ((VacC.sigR ε a : ℝ) : ℂ) ^ 2 / (c : ℂ)) = fun _ _ => (c : ℂ) := by
    funext a j
    rw [sigR_sq, hs']
    field_simp
  rw [hγ]
  simp only [VacS.DG, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← pow_mul, mul_comm n m]

end PositivityTheory.Rg.Sw.Glob.NbarH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def LeviTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∃ (C : ℂ) (A : Mx D n n),
      compAt θ τ A = a ∧ (∀ τ', τ' ≠ τ → compAt θ τ' A = 1) ∧ A.map (finPart D) = 1 ∧
      ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n), (ω (ι y) Φ).1 x = C * Φ.1 (HMul.hMul x A : Mx D V.rank n)

theorem opGen_of' (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) : OpGen := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  obtain ⟨hadd, hcmul, hrmul, hphase, f₁, hf₁, hf₁0⟩ := hS V.rank n
  have unip : ∀ (b : Matrix (Fin n) (Fin n) ℂ) (y' : GR n), bᴴ = b → mR y' = nU b →
      ∀ (Ψ' : Mx D V.rank n → ℂ) (hΨ' : AwayCls θ τ fr Ψ') (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
      (ω (ι y') ⟨tens θ τ fr f Ψ', hΨ'.2 f hf⟩).1 =
        tens θ τ fr (fun u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u) Ψ' := by
    intro b y' hb hy' Ψ' hΨ' f hf
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y' b hb hy']
    show _ * tens θ τ fr f Ψ' x = _
    simp only [tens]
    ring
  rcases hy with ⟨b, hb, hyb⟩ | ⟨c, hc, hyc⟩ | ⟨a, ha, hya⟩
  · exact ⟨fun f u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u,
      fun f hf => hphase ε (tLoc l τ) b f hb hf, fun Ψ hΨ f hf => unip b y hb hyb Ψ hΨ f hf⟩
  · obtain ⟨w, hw⟩ := hW D n
    have hcn : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
    obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hcn
    have hconj := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
    have hy' : ι y = w * ι yn * w⁻¹ := by rw [hconj]; group
    obtain ⟨κ, Aop, A'op, hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
    have hsch : ∀ f, IsSch f → IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧
        IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) := fun f hf =>
      ⟨((hFT 0 (OG.awayCls_zero τ fr)).2.2 f hf).1, ((hFT 0 (OG.awayCls_zero τ fr)).2.2 f hf).2.1⟩
    have step : ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ)
          (fun u' => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u').trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f u')) u) (Aop (A'op Ψ)) ∧
        tens θ τ fr f Ψ = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ)
          (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f u') u) (Aop (A'op Ψ)) := by
      intro Ψ hΨ f hf
      obtain ⟨-, hA', hfs⟩ := hFT Ψ hΨ
      obtain ⟨-, s2, -, e2⟩ := hfs f hf
      obtain ⟨-, -, hfs'⟩ := hFT (A'op Ψ) hA'
      have sP := hphase ε (tLoc l τ) (-c) _ hcn s2
      have e1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
          ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A'op Ψ), hA'.2 _ s2⟩ := Subtype.ext e2
      have e4 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A'op Ψ), hA'.2 _ s2⟩ =
          ⟨_, hA'.2 _ sP⟩ := Subtype.ext (unip (-c) yn hcn hyn (A'op Ψ) hA' _ s2)
      obtain ⟨-, -, e5, -⟩ := hfs' _ sP
      obtain ⟨-, -, e6, -⟩ := hfs' _ s2
      constructor
      · rw [hy', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, e4]
        exact e5
      · have hid : ω w (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩) = ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [e1] at hid
        rw [← e6, hid]
    refine ⟨fun g u => (κ * ftLoc ε (tLoc l τ) (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f₁ u') 0)⁻¹ *
        (κ * ftLoc ε (tLoc l τ) (fun u' => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u').trace) *
          (κ⁻¹ * ftLoc ε (-tLoc l τ) g u')) u), fun g hg => ?_, fun Ψ hΨ f hf => ?_⟩
    · exact hcmul _ _ (hsch _ (hphase ε (tLoc l τ) (-c) _ hcn (hsch g hg).2)).1
    · set c₀ := κ * ftLoc ε (tLoc l τ) (fun u' => κ⁻¹ * ftLoc ε (-tLoc l τ) f₁ u') 0 with hc₀
      have hAA : AwayCls θ τ fr (Aop (A'op Ψ)) := (hFT (A'op Ψ) (hFT Ψ hΨ).2.1).1
      have hrel : ∀ x, Ψ x = c₀ * Aop (A'op Ψ) x := by
        intro x
        obtain ⟨x', hx1, hx2, hx3⟩ := OG.exists_slice hC.hθ τ x (0 : Matrix (Fin V.rank) (Fin n) ℂ)
        have e := congrFun (step Ψ hΨ f₁ hf₁).2 x'
        have hz0 : fr⁻¹ * compAt θ τ x' = (0 : Fin V.rank → Fin n → ℂ) := by
          rw [hx1]; exact Matrix.mul_zero _
        simp only [tens] at e
        rw [hz0, hf₁0, one_mul] at e
        rw [← hΨ.1 x' x hx2 hx3, ← hAA.1 x' x hx2 hx3]
        exact e
      by_cases hz : c₀ = 0
      · have hΨ0 : ∀ x, Ψ x = 0 := fun x => by rw [hrel x, hz, zero_mul]
        have h00 : (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := by
          apply Subtype.ext
          funext x
          simp [tens, hΨ0 x]
        rw [h00, map_zero]
        funext x
        simp [tens, hΨ0 x]
      · rw [(step Ψ hΨ f hf).1]
        funext x
        simp only [tens]
        rw [hrel x]
        field_simp
  · obtain ⟨C, A, hA1, hA2, hA3, hact⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
    refine ⟨fun f u => C * f (Matrix.of u * a), fun f hf => hcmul C _ (hrmul a f ha hf), ?_⟩
    intro Ψ hΨ f hf
    funext x
    rw [hact]
    have hcomp : compAt θ τ (HMul.hMul x A : Mx D V.rank n) = compAt θ τ x * a := by
      rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
    have hPsi : Ψ (HMul.hMul x A : Mx D V.rank n) = Ψ x := by
      apply hΨ.1
      · intro τ' hτ'
        rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' hτ', Matrix.mul_one]
      · rw [Matrix.map_mul, hA3, Matrix.mul_one]
    show C * tens θ τ fr f Ψ (HMul.hMul x A : Mx D V.rank n) = tens θ τ fr (fun u => C * f (Matrix.of u * a)) Ψ x
    simp only [tens]
    rw [hcomp, hPsi, ← Matrix.mul_assoc, mul_assoc]
    rfl

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SummableOfAbsTheta
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem summable_of_absTheta {D : D7} {V : HSp D} {n : ℕ} (φ : Mx D V.rank n → ℂ) (h : GA D V)
    (hh : GlobalTheory.SiegelFormula.absTheta V φ h < ⊤) :
    Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => φ (GlobalTheory.SiegelFormula.invPt V h ξ) :=
  Summable.of_enorm hh.ne

theorem thLin_of (hP : GlobalTheory.Published.WeilThetaConvergence) : ThLin := by
  intro D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g
  obtain ⟨h1, h2, hr⟩ := hR
  have hn : 1 ≤ n := by omega
  have hI := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g
  have hI' := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g
  have hae : ∀ φ : schwartzA θ V.rank n,
      ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ := by
    intro φ
    have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ
    have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hS.hθ _ _ φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1
    exact ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
  have heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν]
      fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q := by
    filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'
    simp only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢
    have s1 := summable_of_absTheta (ω g Φ).1 _ hq
    have s2 := summable_of_absTheta (ω g Φ').1 _ hq'
    show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) =
      (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)
    rw [← s1.tsum_add s2]
    congr 1
    funext ξ
    simp [map_add]
  unfold thetaInt
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq,
    integral_add hI hI', smul_add]

end PositivityTheory.Rg.Sw.Glob
end
end

