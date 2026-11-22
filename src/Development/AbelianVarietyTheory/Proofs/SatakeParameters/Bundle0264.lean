import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.Bundle0063
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

variable (St) in

abbrev StepDatum (i : ℕ) (hi : i + 1 ≤ D.R.m) : Type :=
  (St i (Nat.le_of_succ_le hi)).Ch → (St (i + 1) hi).Ch →
    UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → HomE D.host.E (D.R.N i) (D.R.N (i + 1)) → ℂ

structure MuLaws (_A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) : Prop where
  mu_read : ∀ i < D.R.m, ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
    muT (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)
  mu_cls : ∀ i < D.R.m, ∀ k hk c, muT (i + 1) (Matrix.GeneralLinearGroup.det ((St k hk).y c).1) =
    (((t.O u μ).mt (i + 1) ((t.O u μ).dt k c) : ℂˣ) : ℂ)
  mu_mul : ∀ i < D.R.m, muT (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), muT (i + 1) (x * y) = muT (i + 1) x * muT (i + 1) y
  mu_alg : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), muT (i + 1) x ∈ TaylorLogMetric.Qbar
  mu_unr : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
    (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muT (i + 1) x = 1
  mu_rat : ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
    ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
      muT (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

variable (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

structure StepLaws (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) (i : ℕ) (hi : i + 1 ≤ D.R.m) (Xi : StepDatum St i hi) : Prop where
  read : ∀ c c' z, Xi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') ((St i (Nat.le_of_succ_le hi)).y c) ((St (i + 1) hi).y c') z =
    (t.rd u μ).Xi i c c' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  rat : ∀ β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, Xi β β' x₁ x₁' z = Xi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  lev : ∀ β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * Xi β β' x₁ x₁' z =
      muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * Xi β β' x x' z
  away : ∀ β β' x x' x₁ x₁',
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → Xi β β' x₁ x₁' = Xi β β' x x'
  loc : ∀ β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (Xi β β' x x')
  supp : ∀ β β' x x' z, Xi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))
  int : ∀ β β' x x' z, IntOff (t.O u μ).S (Xi β β' x x' z)

variable {A dtU a}

end Split

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicRingEquivEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Topology Filter

theorem adic_ringEquiv_eq_self {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (ψ : w.adicCompletion F ≃+* w.adicCompletion F)
    (hF : ∀ a : F, ψ (algebraMap F _ a) = algebraMap F _ a)
    (hO : ∀ y, y ∈ w.adicCompletionIntegers F ↔ ψ y ∈ w.adicCompletionIntegers F) (y : w.adicCompletion F) :
    ψ y = y := by
  have hval : ∀ b : F, Valued.v (algebraMap F (w.adicCompletion F) b) = w.valuation F b := by
    intro b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

  have hcmp : ∀ (b : F) (u : w.adicCompletion F), b ≠ 0 →
      (Valued.v u ≤ Valued.v (algebraMap F (w.adicCompletion F) b) ↔
        Valued.v (ψ u) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)) := by
    intro b u hb
    have hb' : (algebraMap F (w.adicCompletion F) b) ≠ 0 := by simpa using hb
    have hpos : 0 < Valued.v (algebraMap F (w.adicCompletion F) b) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb')
    have h1 := hO (u / algebraMap F _ b)
    rw [map_div₀, hF, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_div₀, div_le_one₀ hpos,
      div_le_one₀ hpos] at h1
    exact h1

  have hball : ∀ (b : F) (z : w.adicCompletion F), b ≠ 0 →
      {x : w.adicCompletion F | Valued.v (x - z) ≤ Valued.v (algebraMap F (w.adicCompletion F) b)} ∈ 𝓝 z := by
    intro b z hb
    set t := algebraMap F (w.adicCompletion F) b
    have ht : t ≠ 0 := by simpa [t] using hb
    have hpos : 0 < Valued.v t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)
    have hc : Continuous fun x : w.adicCompletion F => (x - z) / t := by fun_prop
    have ho := (Valued.isOpen_valuationSubring (w.adicCompletion F)).preimage hc
    refine mem_of_superset (ho.mem_nhds ?_) ?_
    · show (z - z) / t ∈ Valued.v.valuationSubring
      rw [sub_self, zero_div]; exact zero_mem _
    · intro x hx
      have hx' : Valued.v ((x - z) / t) ≤ 1 := hx
      rw [map_div₀, div_le_one₀ hpos] at hx'
      exact hx'
  by_contra hne
  have hz0 : ψ y - y ≠ 0 := sub_ne_zero.mpr hne
  have hvz : Valued.v (ψ y - y) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuation_surjective F w (Valued.v (ψ y - y) * WithZero.exp (-1 : ℤ))
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hb
    exact (mul_ne_zero hvz WithZero.exp_ne_zero) hb.symm
  have hbv : Valued.v (algebraMap F (w.adicCompletion F) b) < Valued.v (ψ y - y) := by
    rw [hval, hb]
    exact mul_lt_of_lt_one_right (zero_lt_iff.2 hvz) (by have h : (WithZero.exp (1:ℤ))⁻¹ < 1 := compareOfLessAndEq_eq_lt.mp rfl; simpa using h)
  obtain ⟨_, hx, a, rfl⟩ := mem_closure_iff_nhds.1
    ((HeightOneSpectrum.denseRange_algebraMap F w) y) _ (hball b y hb0)
  have h1 : Valued.v (y - algebraMap F _ a) ≤ Valued.v (algebraMap F (w.adicCompletion F) b) := by
    rw [← Valuation.map_neg, neg_sub]; exact hx
  have h2 := (hcmp b _ hb0).1 h1
  rw [map_sub, hF] at h2
  have h3 : ψ y - y = (ψ y - algebraMap F _ a) - (y - algebraMap F _ a) := by ring
  have h4 := Valuation.map_sub Valued.v (ψ y - algebraMap F _ a) (y - algebraMap F _ a)
  rw [← h3] at h4
  exact absurd (h4.trans (max_le h2 h1)) (not_le.2 hbv)

end GlobalTheory.TwV.Xc

namespace GlobalTheory.TwV.Xc

theorem firstFactor_agree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W Q : Type) [CommRing W] [Field Q] [Algebra W Q] (w w' : HeightOneSpectrum (𝓞 F)) (e : Q ≃+* w.adicCompletion F) (e' : Q ≃+* w'.adicCompletion F) (φ : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F) (φ' : E ⊗[F] w'.adicCompletion F →+* w'.adicCompletion F), (∀ c, φ ((1 : E) ⊗ₜ[F] c) = c) → (∀ c, φ' ((1 : E) ⊗ₜ[F] c) = c) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) → (∀ x : Q, x ∈ Set.range (algebraMap W Q) ↔ e' x ∈ w'.adicCompletionIntegers F) → (∀ a : E, e.symm (φ (a ⊗ₜ[F] 1)) = e'.symm (φ' (a ⊗ₜ[F] 1))) → w = w' ∧ ∀ x : AfE F E, e.symm (φ (prV (E := E) w x)) = e'.symm (φ' (prV (E := E) w' x)) := by
  intro F E _ _ _ _ _ W Q _ _ _ w w' e e' φ φ' hφ hφ' hW hW' hE
  have hF : ∀ a : F, e.symm (algebraMap F _ a) = e'.symm (algebraMap F _ a) := by
    intro a
    have h := hE (algebraMap F E a)
    have h1 : (algebraMap F E a) ⊗ₜ[F] (1 : w.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    have h2 : (algebraMap F E a) ⊗ₜ[F] (1 : w'.adicCompletion F) = (1 : E) ⊗ₜ[F] algebraMap F _ a := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    rwa [h1, h2, hφ, hφ'] at h
  have hO : ∀ x : Q, e x ∈ w.adicCompletionIntegers F ↔ e' x ∈ w'.adicCompletionIntegers F :=
    fun x => (hW x).symm.trans (hW' x)
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (b : F),
      Valued.v (algebraMap F (v.adicCompletion F) b) = v.valuation F b := by
    intro v b
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hww : w = w' := by
    by_contra hne
    have hle : ¬ w.asIdeal ≤ w'.asIdeal := fun h =>
      hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h))
    obtain ⟨b, hbw, hbw'⟩ := Set.not_subset.1 hle
    have key := hO (e.symm (algebraMap F _ (algebraMap (𝓞 F) F b)⁻¹))
    rw [RingEquiv.apply_symm_apply, hF, RingEquiv.apply_symm_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      hval, hval, map_inv₀, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hbw', inv_one] at key
    have h1 : w.intValuation b < 1 := (HeightOneSpectrum.intValuation_lt_one_iff_mem w b).2 hbw
    have h0 : w.intValuation b ≠ 0 :=
      HeightOneSpectrum.intValuation_ne_zero w b (fun h => hbw' (h ▸ w'.asIdeal.zero_mem))
    have := key.2 le_rfl
    exact absurd this (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 h1))
  subst hww
  refine ⟨rfl, ?_⟩
  have hψ := adic_ringEquiv_eq_self w (e.symm.trans e') (fun a => by simp [hF a])
    (fun y => by simpa using hO (e.symm y))
  have hc : ∀ c, e.symm c = e'.symm c := fun c => by
    have h := hψ c
    simp only [RingEquiv.trans_apply] at h
    rw [← e'.symm_apply_apply (e.symm c), h]
  intro x
  generalize prV (E := E) w x = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
      have : a ⊗ₜ[F] c = (a ⊗ₜ[F] (1 : w.adicCompletion F)) * ((1 : E) ⊗ₜ[F] c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, map_mul, map_mul, map_mul, map_mul, hφ, hφ', hE a, hc]
  | add x y hx hy => simp [map_add, hx, hy]

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlacesStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ), IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (exact GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (intros; apply GlobalTheory.Cong.AutFormFix.fixed_intU_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponent
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong

theorem locU_conj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (y : UA E a) {x : UA E a} (hx : x ∈ locU a w) : y * x * y⁻¹ ∈ locU a w := by
  simp only [locU, finU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, map_mul, map_inv] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  exact ⟨by simp [h1], fun u hu => by simp [h2 u hu]⟩

theorem exists_locU_mul_comm {E : Type} [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) (g : UA E a) :
    ∃ x ∈ locU a w, ∃ y : UA E a, g = x * y ∧ ∀ z ∈ locU a w, y * z = z * y := by
  have hb := (GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw).1
  obtain ⟨x, hx⟩ := hb.2 (cLoc w g)
  have hx' : cLoc w (x : UA E a) = cLoc w g := hx
  refine ⟨x, x.2, (x : UA E a)⁻¹ * g, by group, fun z hz => ?_⟩
  have hy : cLoc w ((x : UA E a)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
  have hc := locU_conj_mem w ((x : UA E a)⁻¹ * g) hz
  have he : (⟨_, hc⟩ : locU a w) = ⟨z, hz⟩ := hb.1 (by
    change cLoc w (_ * z * _) = cLoc w z
    rw [map_mul, map_mul, map_inv, hy]; group)
  have he' := congrArg Subtype.val he
  simp only at he'
  calc (x : UA E a)⁻¹ * g * z = ((x : UA E a)⁻¹ * g * z * ((x : UA E a)⁻¹ * g)⁻¹) * ((x : UA E a)⁻¹ * g) := by group
    _ = z * ((x : UA E a)⁻¹ * g) := by rw [he']

theorem span_comp_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  intro E _ _ _ a U hU w hw σ hσ φ hφ
  set S := ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
    f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 with hS
  have hSU : S ≤ U := iSup_le fun f => by
    rintro _ ⟨v, rfl⟩; exact f.2.1 v
  obtain ⟨-, f0, hf0, hf0U, hf0e⟩ := hσ
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hf0
    ext v
    have : f0 v ∈ S := (le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
      f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) ⟨f0, hf0U, hf0e⟩) ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simp [this]

  have hloc : ∀ x : locU a w, ∀ ψ ∈ S, RU E a x ψ ∈ S := by
    intro x ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a x ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      rw [← f.2.2 x v]
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f ⟨_, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; rw [map_add]; exact add_mem h₁ h₂

  have hcen : ∀ y : UA E a, (∀ z ∈ locU a w, y * z = z * y) → ∀ ψ ∈ S, RU E a y ψ ∈ S := by
    intro y hy ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a y ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      let f' : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
          f (σ.ρ (cLoc w x) v) = RU E a x (f v)} :=
        ⟨RU E a y ∘ₗ f.1, fun v => hU.stable y _ (f.2.1 v), fun x v => by
          simp only [LinearMap.comp_apply]
          rw [f.2.2 x v, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hy x x.2]⟩
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f' ⟨v, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; rw [map_add]; exact add_mem h₁ h₂
  have hstab : ∀ g, ∀ ψ ∈ S, RU E a g ψ ∈ S := by
    intro g ψ hψ
    obtain ⟨x, hx, y, rfl, hy⟩ := exists_locU_mul_comm a w hw g
    rw [map_mul, Module.End.mul_apply]
    exact hloc ⟨x, hx⟩ _ (hcen y hy ψ hψ)
  rcases hU.irred S hSU hstab with h | h
  · exact absurd h hS0
  · rw [h]; exact hφ

end GlobalTheory.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockDetResidueCharEqOneOfCongModQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamQBCong

open GlobalTheory.TopStep

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem entry_cong (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (g : HomE E N N)
    (hg : ∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) (s t : Fin N) :
    IntAt P (g (Pi.single t 1) s) ∧ redP P (g (Pi.single t 1) s) = if s = t then 1 else 0 := by
  classical
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hx := mem_stdAt.1 (hg _ (single_mem_stdAt (P := P) t)) s
  set δ : E := (Pi.single t (1 : E) : Sp E N) s with hδ
  have hδI : IntAt P δ := mem_stdAt.1 (single_mem_stdAt (P := P) t) s
  have hdiv : IntAt P ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
    have e : (((qOf P : E)⁻¹ • (g (Pi.single t 1) - Pi.single t 1) : Sp E N)) s = (g (Pi.single t 1) s - δ) / (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [← e]
    exact hx
  have hI : IntAt P (g (Pi.single t 1) s - δ) := by
    have e : g (Pi.single t 1) s - δ = (qOf P : E) * ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
      field_simp
    rw [e]
    exact (intAt_nat _).mul hdiv
  have hI' : IntAt P (g (Pi.single t 1) s) := by
    have := intAt_sub hI (intAt_neg hδI)
    rwa [sub_neg_eq_add, sub_add_cancel] at this
  refine ⟨hI', ?_⟩
  have h0 := redP_eq_zero_of_div hdiv
  rw [reduction_sub hI' hδI, sub_eq_zero] at h0
  rw [h0, hδ, Pi.single_apply]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

theorem lamQB_eq_one_of_cong : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N →
    (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  intro E K _ _ _ _ P ξ kj n N g hn hg
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n - kj)) (Fin (n - kj)) E := Matrix.of fun s t : Fin (n - kj) =>
    Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = g (Pi.single ⟨kj + t.1, ht⟩ 1) ⟨kj + s.1, hs⟩ := by
      rw [hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dif_pos hs]
    obtain ⟨h1, h2⟩ := entry_cong P g hg ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst]
  have hdet : redP P D.det = 1 := by
    rw [(det_int fun s t => (hent s t).1).2]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LamQBCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1Statement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_ext_mem_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  first | exact @GlobalTheory.TopStep.ext_mem_twisted_k1_level | exact GlobalTheory.TopStep.ext_mem_twisted_k1_level | (intros; apply GlobalTheory.TopStep.ext_mem_twisted_k1_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

namespace GlobalTheory.TwU

theorem seamP_under_eq : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  intro D X s hs hX P Q h
  have key : ∀ a : 𝓞 D.host.F, ∃ r : 𝓞 X.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = RingOfIntegers.mapRingEquiv s.iE (algebraMap (𝓞 X.F) (𝓞 X.E) r) := by
    intro a
    set b := (RingOfIntegers.mapRingEquiv s.iE).symm (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) with hb
    have hbe : RingOfIntegers.mapRingEquiv s.iE b = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      rw [hb, RingEquiv.apply_symm_apply]
    have hfix : X.conjO b = b := by
      apply RingOfIntegers.ext
      apply s.iE.injective
      have h1 : s.iE (b : X.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) :=
        congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hbe
      have h2 : ((X.conjO b : 𝓞 X.E) : X.E) = star (b : X.E) := rfl
      rw [h2, hs.2, h1]
      have h3 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [h3, ← Formalism.BasicNotions.Examples₂.star_eq_conj]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := GlobalTheory.TwistPlaces.exists_of_conj_eq hX hfix
    exact ⟨r, by rw [hr, hbe]⟩
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  ext a
  obtain ⟨r, hr⟩ := key a
  have hPQ : r ∈ Ideal.under (𝓞 X.F) P.asIdeal ↔ r ∈ Ideal.under (𝓞 X.F) Q.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  simp only [Ideal.under, Ideal.mem_comap] at hPQ ⊢
  rw [hr, mem_seamP, mem_seamP]
  exact hPQ

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.QCong

theorem conj_extE_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  intro E _ _ _ P n c j D h κ hκ hjD hh x hx
  obtain ⟨m, rfl⟩ : ∃ m, D = j + 1 + m := ⟨D - (j + 1), by omega⟩
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hu := (hh x hx).2
  have hw : GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x) ∈ stdAt E n P :=
    GlobalTheory.TopStep.mem_stdAt.2 fun i => GlobalTheory.TopStep.mem_stdAt.1 hu (Fin.castAdd c i)
  have hw' := (GlobalTheory.TopStep.mem_prinCong.1 hκ) _ hw
  have key : (qOf P : E)⁻¹ • (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) = ((qOf P : E) ^ m) • Loc.inX E n c
      ((((qOf P : E) ^ (j + 1 + m))⁻¹) • (κ.1 (GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x)) - GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x))) := by
    rw [GlobalTheory.CongLevel.extE_apply, add_sub_cancel_left, map_smul (GlobalTheory.CongLevel.resX c), map_smul κ.1, ← smul_sub, smul_smul,
      ← map_smul, ← map_smul, smul_smul]
    congr 2
    field_simp
    ring
  have e1 : (h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x = h⁻¹ (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) := by
    rw [map_sub]
    congr 1
    exact (LinearEquiv.symm_apply_apply h x).symm
  rw [e1, ← map_smul, key]
  refine (hh _ ?_).1
  refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.CongLevel.inX_apply]
  split_ifs with hl
  · exact (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) m).mul (GlobalTheory.TopStep.mem_stdAt.1 hw' _)
  · rw [mul_zero]; exact GlobalTheory.TopStep.intAt_zero

end GlobalTheory.QCong
end

