import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSmallInt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Comb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)

def AlgComb (φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
    φ = ∑ k, z k • evW YS v₀ j (g k).val

variable {YS v₀ j}

theorem AlgComb.zero : AlgComb YS v₀ j 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, by rw [Finset.univ_eq_empty, Finset.sum_empty]⟩

theorem AlgComb.add {φ ψ : GA D (Wc D j) → ℂ} (h1 : AlgComb YS v₀ j φ) (h2 : AlgComb YS v₀ j ψ) :
    AlgComb YS v₀ j (φ + ψ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h1
  obtain ⟨m, z', g', hz', rfl⟩ := h2
  refine ⟨n + m, Fin.append z z', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    · rw [Fin.append_left]; exact hz a
    · rw [Fin.append_right]; exact hz' a
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem AlgComb.smul {φ : GA D (Wc D j) → ℂ} (h : AlgComb YS v₀ j φ) {a : ℂ} (ha : IsAlgebraic ℚ a) :
    AlgComb YS v₀ j (a • φ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h
  refine ⟨n, fun k => a * z k, g, fun k => ?_, ?_⟩
  · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
    exact (hmem _).1 (mul_mem ((hmem _).2 ha) ((hmem _).2 (hz k)))
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _

theorem isAlgebraic_of_smallInt {y : ℂ} (hy : y ∈ GlobalTheory.BigOn.Exp.smallInt D) : IsAlgebraic ℚ y := by
  obtain ⟨a, rfl⟩ := hy
  exact (Algebra.IsAlgebraic.isAlgebraic (algebraMap (𝓞 ↥D.LL0) ↥D.LL0 a)).algHom (embLL0 D).toRatAlgHom

theorem algComb_of_small {ρ : Setup D.ntw} {i : D.ntw.Tw} {b : Bool}
    (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → AlgComb YS v₀ j (Φ P))
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h) :
    AlgComb YS v₀ j (Φ P) := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (GlobalTheory.BigOn.Exp.smallInt D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ AlgComb YS v₀ j (Φ P') := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, by rw [map_zero]; exact AlgComb.zero⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, by rw [map_add]; exact f₁.add f₂⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      refine ⟨(c : ℂ) • P₁, Submodule.smul_mem _ _ a1, ?_, ?_⟩
      · rw [map_smul]; rfl
      · rw [map_smul]; exact f₁.smul (isAlgebraic_of_smallInt c.2)
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Comb

end GlobalTheory.SerRefCore

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem isAlgebraic_of_mem {L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] {z : ℂ} (hz : z ∈ L) : IsAlgebraic ℚ z :=
  IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨z, hz⟩ : L))

theorem algComb_of_ratScalar (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν)
    (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) :
    ρ.IsDatum i j b s h P → P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h →
      AlgComb YS v₀ j (ν • ρ.theta i j b h P) := by
  intro hd hPl
  have hti := tieIn_of_fw fw
  have hrd := readsAs_one YS fw hev hV
  obtain ⟨gR, cR, cL, -, u, hu, c, ph, -, -, rfl, hsc, hrat⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b

  obtain ⟨nδ, hnδ, hδ⟩ := de_values hρ i j b
  have hcard : Nat.card (ρ.B i j b).G.P.H ≠ 0 := Nat.card_pos.ne'
  haveI := GlobalTheory.CoverSmall.smallF_normal D hgal
  let K : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield
  have hK : ∀ {z : ℂ} {m : ℕ}, m ≠ 0 → z ^ m = 1 → z ∈ K := fun hm hz =>
    mem_algebraicClosure_iff.2 (GlobalTheory.BigOn.Exp.isAlgebraic_of_pow_eq_one hm hz)
  obtain ⟨L, _, _, hL0, -, hLr⟩ := exists_normal_roots (GlobalTheory.CoverSmall.smallF D) (k := K)
    (fun z hz => mem_algebraicClosure_iff.2 (isAlgebraic_of_mem hz)) (mul_ne_zero hcard hnδ)
  obtain ⟨C, hpd, hfr, hC⟩ := exists_goodCover_pdAt YS hRF hT hti.alg hval hray hsp (D.ntw.l i) j (κ j).n L hL0
  have hLL : (embLL0 D).fieldRange ≤ C.σ₂.fieldRange := by
    rw [hfr]; exact fun z hz => hL0 hz
  have hdat := isLevDatum_vecBase YS hT hcore hgal hval hroots hsp hρ hpin i j b hLL
    (fun p => by
      have hp1 : (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
    (fun x => by
      have hp1 : (((ρ.B i j b).de.chi x : Circle) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul', (hδ x).1, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
  rw [← hpd] at hdat
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi := by
    rw [hpd]; exact isTwist_delAt Rl.C hval _ (hpin.delta i j b) hLL
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta] at h1
    exact h1

  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm
  refine algComb_of_small ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h) hinj (fun G => ?_) (fun P hP G hPG => ?_) hPl
  · have h3 : coefFn (embLL0 D) (ρ.B i j b).w.lam (G : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) ∈
        (harm (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS).map (harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ _ _ hB.wt hm]
      exact Submodule.subset_span ⟨GlobalTheory.CoefModel.mapVV (embLL0 D) _ G, (Scale.coefFn_map _ _ _).symm⟩
    exact h3
  · obtain ⟨G', hG', hPG'⟩ : ∃ G' : VV D.what₂.LL (FWT.lamV D j),
        (∀ m, D.what₂.embLL (MvPolynomial.coeff m (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈ (embLL0 D).fieldRange) ∧
        harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
          coefFn D.what₂.embLL (FWT.lamV D j) (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
      rw [hPG]
      have hlam := hBo.lam
      generalize (ρ.B i j b).w.lam = lam at G hlam
      subst hlam
      refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV D.LL0.val.toRingHom _ _ G.2⟩, fun m => ⟨MvPolynomial.coeff m G.1, ?_⟩, ?_⟩
      · exact congrArg D.what₂.embLL (MvPolynomial.coeff_map D.LL0.val.toRingHom G.1 m).symm
      · rw [← Scale.coefFn_map, ← Scale.coefFn_map D.what₂.embLL]
        exact congrArg _ (MvPolynomial.map_map _ _ _).symm
    have hP' := hsc.ioP_eq hinj hP (ioP_mem_valSpace hcore hio (hti.hv₀ j _) hB hBo hu _) hPG'
    have hR := ((hrat C hC hLL h hd.fin _ hdat (cL j G') (Submodule.subset_span ⟨G', fun m => hLL (hG' m), rfl⟩)).2 _ _ htw).2 _ hω'
    replace hR : IsRat T j hV C (κ j) ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h P) :=
      (congrArg (IsRat T j hV C (κ j)) (hpin.phase_mul_thetaKO i b hP' ph (ρ.om i j b 1) h (ρ.B i j b).vecBase)).mp hR
    obtain ⟨n, z, x, hz, e⟩ := exists_sum_evW YS hti hnV hcore.lev hpb hrd hC hR fun k hk g => by
      have := GlobalTheory.ExportType.theta_type hB (D.sp.V_sig _) hω (one_mem _) (lifts_one hBo hk) h P g
      rw [show (⟨1, one_mem _⟩ : (ρ.B i j b).G.P.H) = 1 from rfl, map_one, Units.val_one, one_mul] at this
      exact congrArg ((ph * c) * ·) this
    refine ⟨n, z, x, fun k => ?_, ?_⟩
    · have hzk : z k ∈ L := by
        have := hz k
        rw [hfr] at this
        exact this
      exact isAlgebraic_of_mem hzk
    · rw [LinearMap.smul_apply, e, one_smul]

end Main

end GlobalTheory.SerRefCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.MultScale

variable {p : ℕ} [Fact p.Prime]

def EFA (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem EFA_tmul (D : Datum p) (a a' : AfP p) (x x' : D.La) :
    EFA D (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ x')) = a * a' * ((D.EF x x' : ℤ) : AfP p) := by
  simp only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]
  rw [Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]

theorem EFA_inAf (D : Datum p) (x y : D.La) : EFA D (inAf D x) (inAf D y) = ((D.EF x y : ℤ) : AfP p) := by
  rw [inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]

theorem isIntAf_intCast (z : ℤ) : IsIntAf ((z : AfP p)) := fun v => by
  rw [map_intCast]; exact intCast_mem _ z

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isIntAf_zero : IsIntAf (0 : AfP p) := by simpa using isIntAf_intCast (p := p) 0

theorem isIntAf_EFA (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (EFA D v w) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      rw [EFA_tmul]; exact isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)
    | zero => simpa using isIntAf_zero
    | add u u' _ _ h h' => rw [map_add]; exact isIntAf_add h h'
    | neg u _ h => rw [map_neg]; exact isIntAf_neg h
  | zero => simpa using isIntAf_zero
  | add u u' _ _ h h' => rw [map_add, LinearMap.add_apply]; exact isIntAf_add h h'
  | neg u _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

section Sim

variable {D : Datum p} {G : HTGroup p}

theorem bc_adj {V : Type} [AddCommGroup V] [Module ℚ V] (A : Type) [CommRing A] [Algebra ℚ A]
    (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V) (h : ∀ v w, B (f v) w = B v (g w)) (v w : A ⊗[ℚ] V) :
    B.baseChange A (f.baseChange A v) w = B.baseChange A v (g.baseChange A w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (c : C) :
    actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
  rw [Algebra.smul_def]
  first
  | exact Algebra.TensorProduct.lift_tmul _ _ _ r c
  | (erw [Algebra.TensorProduct.lift_tmul]; rfl)
  | rfl

theorem EFA_actOn (L : Link D G) (X : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (actOn L.rep (AfP p) X v) w = EFA D v (actOn L.rep (AfP p) (starT G.star (AfP p) X).unop w) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add X X' hX hX' => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, hX, hX']
  | tmul r c =>
    rw [starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w

theorem EFA_actG (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (L.actG g v) (L.actG g w) = ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * EFA D v w := by
  obtain ⟨⟨u, c⟩, hmem⟩ := g
  have h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p) := hmem
  have h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p) := by
    have e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        algebraMap (AfP p) _ (c : AfP p) := by
      rw [← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z := fun z => rfl
  rw [hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply,
    map_smul, smul_eq_mul]
  rfl

end Sim

theorem isIntAf_one : IsIntAf (1 : AfP p) := by simpa using isIntAf_intCast (p := p) 1

theorem inAf_mem (D : Datum p) (z : D.La) : inAf D z ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩

end GlobalTheory.LKGeo.MultScale

namespace GlobalTheory.LKGeo

end GlobalTheory.LKGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocus
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.FnInt

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  intro k _ X _ p D hA P e x hG l w hl hw
  have : IsProper p := by
    obtain ⟨m, i, hi, rfl⟩ := hA.isProjOver
    have := isProper_str k m
    infer_instance
  have hmem : w ∈ (integralClosure (Subring.closure (Set.range fun j => x j / x l)) X.functionField).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    rintro ⟨V, hV⟩
    change w ∈ V
    have hk : ∀ a : k, toFunctionField p a ∈ V := by
      intro a
      have := hA.finite
      have h1 : IsIntegral ℤ (toFunctionField p a) :=
        (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (toFunctionField p).toIntAlgHom
      have h2 : IsIntegral V (toFunctionField p a) := h1.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      rw [← hy]; exact y.2
    have hd := dominatesStalk_centre p V hk
    obtain ⟨j, hj⟩ := hG.cover (centre p V hk)
    have hz : centre p V hk ∈ NV P e 0 (x l) := by
      intro i i' hi hi'
      have hu := hj i i' hi hi'
      have hr := hG.mem l (centre p V hk) i i' hi hi'
      have hne := hu.ne_zero
      have hxj : x j ≠ 0 := fun h0 => hne (by simp [Pair.loc, h0])
      have hloc : P.loc (e : ℤ) 0 (x l) i i' = x l / x j * P.loc (e : ℤ) 0 (x j) i i' := by
        simp only [Pair.loc]; field_simp
      have hg : RegAt (centre p V hk) (x l / x j) := by
        have : x l / x j = P.loc (e : ℤ) 0 (x l) i i' * (P.loc (e : ℤ) 0 (x j) i i')⁻¹ := by
          rw [hloc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
        rw [this]; exact hr.mul hu.inv.regAt
      have hgu : UnitAt (centre p V hk) (x l / x j) := by
        by_contra hn
        obtain ⟨a, ha, hag⟩ := zeroAt_iff.2 ⟨hg, hn⟩
        have h1 := hd.2 a ha
        rw [hag] at h1
        have hgV : x l / x j ∈ V := by rw [← hag]; exact hd.1 a
        have h2 : (x l / x j)⁻¹ ∈ V := by
          rw [inv_div]; exact hV ⟨j, rfl⟩
        have hgne : x l / x j ≠ 0 := div_ne_zero hl hxj
        have hu' : IsUnit (⟨x l / x j, hgV⟩ : V) := by
          refine ⟨⟨⟨_, hgV⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ hgne), Subtype.ext (inv_mul_cancel₀ hgne)⟩, rfl⟩
        exact (V.coe_mem_nonunits_iff (a := ⟨_, hgV⟩)).mp h1 hu'
      rw [hloc]; exact hgu.mul hu
    obtain ⟨a, ha⟩ := hw _ hz
    rw [← ha]; exact hd.1 a
  exact hmem

end GlobalTheory.FnInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_setOf_intAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) :
    IsOpen {x : X | IntAt L α s x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨j, W, hW, hx, hWa, hint⟩
  exact ⟨W, fun x' hx' => ⟨j, W, hW, hx', hWa, hint⟩, W.isOpen, hx⟩

theorem exists_fibre_generic {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyIrreducible f] (y : S) :
    ∃ ζ : X, f ζ = y ∧ ∀ z, f z = y → ζ ⤳ z := by
  refine ⟨f.fiberι y (genericPoint (f.fiber y)), ?_, ?_⟩
  · have : f.fiberι y (genericPoint (f.fiber y)) ∈ Set.range (f.fiberι y) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range (f.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hz
    exact (genericPoint_specializes z').map (f.fiberι y).continuous

theorem exists_specializes_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R)
    (y : M.S) : ∃ y₀, y ⤳ y₀ ∧ M.π y₀ = closedPoint R := by
  haveI := M.proper
  have hc : IsClosed (M.π '' closure {y}) := M.π.isClosedMap _ isClosed_closure
  have hm : M.π y ∈ M.π '' closure {y} := ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (M.π y)).mem_closed hc hm
  exact ⟨y₀, specializes_iff_mem_closure.2 hy₀, e⟩

end GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hcl x
  haveI := hsm; haveI := hgi
  by_contra hx
  obtain ⟨ζ, hζ, hζg⟩ := exists_fibre_generic G.hom (G.hom x)
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_specializes_closedPoint M (G.hom ζ)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G.hom g₀ = y₀ := by
    obtain ⟨g₀, hg₀, -⟩ := exists_fibre_generic G.hom y₀
    exact ⟨g₀, hg₀⟩
  obtain ⟨g, hg, hgg₀⟩ := Flat.generalizingMap G.hom (show G.hom ζ ⤳ G.hom g₀ from hg₀ ▸ hy₀)
  have hζg' : ζ ⤳ g := hζg g (hgg₀.trans hζ)
  have hnζ : ¬ IntAt L α s ζ := fun h => hx (GlobalTheory.T.integral_of_integral_at_fibre_generic_point R M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hζg h)
  have hclosed : IsClosed {z : G.left | ¬ IntAt L α s z} := (isOpen_setOf_intAt L α s).isClosed_compl
  have : ¬ IntAt L α s g₀ := (hζg'.trans hg).mem_closed hclosed hnζ
  exact this (hcl g₀ (by rw [hg₀, hy₀c]))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem isOpen_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU E n)) := by
  intro E _ _ _ hU n S K' hK
  have hT : {w : Pl E | ¬ K' w = KL n w}.Finite := Filter.eventually_cofinite.1 hK.2
  let f : ∀ w : Pl E, finU E n → UL n w := fun w x => ⟨cLoc w x.1, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w x.1⟩
  have hf : ∀ w, Continuous (f w) := fun w =>
    Continuous.subtype_mk ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val) _
  have h1 : ∀ w, f w 1 = 1 := fun w => Subtype.ext (by simp [f])
  have hA : ∀ᶠ k : finU E n in nhds 1, ∀ w : Pl E, cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
    filter_upwards [(UpperTheory.unitaryAdelic_localComponents_continuous_levels_open E n).2.2] with k hk w
    exact (SetLike.ext_iff.1 (GlobalTheory.SmGL.SphCompletion.KO_completion w n) _).1 (hk w)
  have hB : ∀ᶠ k : finU E n in nhds 1, ∀ w ∈ {w : Pl E | ¬ K' w = KL n w}, f w k ∈ K' w := by
    refine (Filter.eventually_all_finite hT).2 fun w _ => ?_
    have ho : IsOpen ((f w) ⁻¹' (K' w : Set (UL n w))) := ((hK.1 w).1).preimage (hf w)
    exact ho.mem_nhds (by simp [h1])
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hA, hB] with x hxA hxB
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun _ => ?_
  refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨f w x, ?_, rfl⟩)
  by_cases hw : K' w = KL n w
  · rw [hw]
    exact Subgroup.mem_subgroupOf.2 (hxA w)
  · exact hxB w hw

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismAdmissibleConnectionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_admissible_connection : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    ∃ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  first | exact @GlobalTheory.JetLiftMain.exists_jetLift | exact GlobalTheory.JetLiftMain.exists_jetLift | (intros; apply GlobalTheory.JetLiftMain.exists_jetLift <;> assumption)
end

