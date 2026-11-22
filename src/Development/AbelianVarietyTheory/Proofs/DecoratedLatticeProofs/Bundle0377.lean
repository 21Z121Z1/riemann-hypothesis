import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.SplitGen

variable {D : D7}

theorem xiN_smul (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    (c : ℂ) (f : WO S T → ℂ) : xiN θ S T hS hT δ sc (c • f) = c • xiN θ S T hS hT δ sc f := by
  funext z
  simp only [xiN, Pi.smul_apply, smul_eq_mul]
  ring

theorem xiN_sum (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ) :
    xiN θ S T hS hT δ sc (∑ i ∈ s, F i) = ∑ i ∈ s, xiN θ S T hS hT δ sc (F i) := by
  funext z
  simp only [xiN, Finset.sum_apply, Finset.mul_sum]

theorem cartan_of_gram (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have e : gramAt D V τ = 1 := by
    unfold gramAt; rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e]
  exact ⟨by simp, by simp, by
    open scoped ComplexOrder in simpa using Matrix.PosDef.one⟩

theorem toHom_sub (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    toHom S T hS hT (γ - γ') = toHom S T hS hT γ - toHom S T hS hT γ' := by
  unfold toHom
  rw [← map_sub]
  rfl

theorem heisO_add_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {x l : WO S T} {X : WO S T → ℂ}
    (h2 : heisO ψ S T (2 • l) X = X) (hph : ψ (symplO S T x l) = 1) :
    heisO ψ S T (x + 2 • l) X = heisO ψ S T x X := by
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ x (2 • l) X
  rw [h2] at h1
  have h3 : ψ (symplOH S T x (2 • l)) = 1 := by
    rw [two_nsmul]
    have e : symplOH S T x (l + l) = symplOH S T x l + symplOH S T x l := by
      simp only [symplOH, GlobalTheory.LatVac.symplO_add_right, mul_add]
    rw [e, ψ.map_add_eq_mul]
    exact GlobalTheory.LatVac.char_half hph
  rw [h1, h3, one_smul]

set_option maxHeartbeats 1600000 in

theorem moves_reading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove
    A₁ A₂ hA₁ hA₂ hA₂γ hsd hα₁ hα₂ hidx f hf hfix₁ hfix₂ hne
  classical
  have hψ := hW.std
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he

  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T μ μ om hW hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) _ _ _ _ s s' (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs])
    (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs']) hmove f hf
  have hdΛ : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS hΛT hu hu'
  have hdΛ' : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS' hΛT' hu hu'
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hoff : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      (1 - (e + cA D e)) • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [GlobalTheory.SplitScalar.off_smul_actO hs hs', sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  have hfo : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.LatVac.finTens 1 γ) := fun γ => (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl
  have hzsub : ∀ γ γ', embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT γ') =
      embH (tauE D) δ (toHom S T hS hT (γ - γ')) := fun γ γ' => by rw [toHom_sub, map_sub]
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set Λ' := (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ'

  have : (A₁.addSubgroupOf A₂).FiniteIndex := ⟨hidx⟩
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hch : ∀ c : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ γ, ((Quotient.out c : A₂) : VCx D.what₂.Tau a b) =
      embH (tauE D) δ (toHom S T hS hT γ) := fun c => hA₂γ _ (Quotient.out c).2
  choose γc hγc using hch
  have hcov : ∀ u ∈ Λ', ∃ c ∈ (Finset.univ : Finset (A₂ ⧸ A₁.addSubgroupOf A₂)),
      u - GlobalTheory.LatVac.finTens 1 (γc c) ∈ Λ := by
    intro u hu
    obtain ⟨γ, l, hl, hl', hγ⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' u hu
    have hx' : GlobalTheory.LatVac.finTens 1 γ ∈ Λ' := by
      rw [show GlobalTheory.LatVac.finTens 1 γ = u - 2 • l by rw [← hγ, sub_sub_cancel]]
      exact sub_mem hu (nsmul_mem hl' 2)
    have hz : embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂ := (hA₂ γ _ (hfo γ)).1 hx'
    refine ⟨QuotientAddGroup.mk (⟨_, hz⟩ : A₂), Finset.mem_univ _, ?_⟩
    have hq : embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) ∈ A₁ := by
      rw [← hγc]
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (A₁.addSubgroupOf A₂) (⟨_, hz⟩ : A₂)
      rw [hh, AddSubgroup.coe_add, sub_add_cancel_left]
      exact neg_mem (AddSubgroup.mem_addSubgroupOf.1 h.2)
    rw [hzsub] at hq
    have h1 := (hA₁ _ _ (hfo _)).2 hq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    have e1 : u - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂))) =
        2 • l + (GlobalTheory.LatVac.finTens 1 γ - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) := by
      rw [← hγ]; abel
    rw [e1]
    exact add_mem (nsmul_mem hl 2) h1
  obtain ⟨R, hR, hRu⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf e u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  obtain ⟨R', hR', hRu'⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf (cA D e) u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  have hRu2 : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ := fun u hu hue => hRu u ⟨hu, hue⟩
  have hRu2' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ := fun u hu hue => hRu' u ⟨hu, hue⟩
  have hmain := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T μ μ om hW hP.inf hP.sigS hP.sigT
    (fun _ => 1) (fun _ => 1) (cartan_of_gram S hP.gS) (cartan_of_gram T hP.gT) ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT'
    e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove R R' hR hRu2 hR' hRu2' f hf

  have hpair : ∀ p : WO S T × WO S T, ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ l : WO S T,
      p ∈ R ×ˢ R' → (l ∈ Λ ∧ l ∈ Λ' ∧ p.1 + p.2 - GlobalTheory.LatVac.finTens 1 γ = 2 • l) := by
    intro p
    by_cases hp : p ∈ R ×ˢ R'
    · obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
      obtain ⟨γ, l, h1, h2, h3⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' (p.1 + p.2)
        (add_mem (hR _ hu).1 (hR' _ hu').1)
      exact ⟨γ, l, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose γ l hγl using hpair
  have hxeq : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) = p.1 + p.2 - 2 • l p := fun p hp => by
    rw [← (hγl p hp).2.2, sub_sub_cancel]
  have hxΛ' : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) ∈ Λ' := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    rw [hxeq p hp]
    exact sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (nsmul_mem (hγl p hp).2.1 2)
  have hwx : ∀ p ∈ R ×ˢ R', p.1 + p.2 = GlobalTheory.LatVac.finTens 1 (γ p) + 2 • l p := fun p hp => by
    rw [hxeq p hp, sub_add_cancel]
  have hz₂ : ∀ p ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₂ := fun p hp =>
    (hA₂ _ _ (hfo _)).1 (hxΛ' p hp)

  have hpf : ∀ p ∈ R ×ˢ R', heisO ψ S T p.1 (heisO ψ S T p.2 f) =
      ψ (symplOH S T p.1 p.2) • heisO ψ S T (GlobalTheory.LatVac.finTens 1 (γ p)) f := by
    intro p hp
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hf.2.lat.1 _ (hγl p hp).1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)]

  have hph : ∀ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) = alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    have hF : heisO ψ S T p.1 (heisO ψ S T p.2 (om (s, s') f)) = om (s, s') f := by
      rw [hom.2.lat.2 _ he' p.2 (hR' _ hu').1 (hR' _ hu').2, hom.2.lat.2 _ he p.1 (hR _ hu).1 (hR _ hu).2]
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hom.2.lat.1 _ (hγl p hp).2.1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)] at hF
    have hG := congrArg (xiN θ S T hS hT δ sc) hF
    rw [xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hom.2.theta _ _ (hfo _)] at hG
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hG w
    have h2 := hfix₂ _ (hz₂ p hp) w
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
    have hU : Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc (om (s, s') f)) w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact hw h1.symm
    exact mul_right_cancel₀ hU (h1.trans h2.symm)

  have hinj : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) -
      embH (tauE D) δ (toHom S T hS hT (γ q)) ∈ A₁ → p = q := by
    intro p hp q hq hpq
    rw [hzsub] at hpq
    have h1 := (hA₁ _ _ (hfo _)).2 hpq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    by_contra hne'
    refine GlobalTheory.SplitScalar.sum_sub_notMem he hst hstc hR hRu2 hR' hRu2' hu hv hu' hv'
      (by rw [Prod.mk.eta, Prod.mk.eta]; exact hne') ?_
    have e2 : p.1 + p.2 - (q.1 + q.2) = (GlobalTheory.LatVac.finTens 1 (γ p) - GlobalTheory.LatVac.finTens 1 (γ q)) +
        2 • (l p - l q) := by
      rw [hwx p hp, hwx q hq]; abel
    rw [e2]
    exact add_mem h1 (nsmul_mem (sub_mem (hγl p hp).1 (hγl q hq).1) 2)
  have hsurj : ∀ y ∈ A₂, ∃ p ∈ R ×ˢ R', y - embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₁ := by
    intro y hy
    obtain ⟨γ₀, rfl⟩ := hA₂γ y hy
    have hv : GlobalTheory.LatVac.finTens 1 γ₀ ∈ Λ' := (hA₂ _ _ (hfo _)).2 hy
    have hh1 : IsHalf e (e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he.1])
    have hh2 : IsHalf (cA D e) (cA D e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he'.1])
    obtain ⟨r, ⟨hr, hrΛ⟩, -⟩ := hRu2 _ (hst' _ hv) hh1
    obtain ⟨r', ⟨hr', hrΛ'⟩, -⟩ := hRu2' _ (hstc' _ hv) hh2
    have hp : (r, r') ∈ R ×ˢ R' := Finset.mem_product.2 ⟨hr, hr'⟩
    refine ⟨(r, r'), hp, ?_⟩
    rw [hzsub]
    refine (hA₁ _ _ (hfo _)).1 ?_
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub, hxeq _ hp]
    have e3 : GlobalTheory.LatVac.finTens 1 γ₀ - ((r, r').1 + (r, r').2 - 2 • l (r, r')) =
        (e • GlobalTheory.LatVac.finTens 1 γ₀ - r) + (cA D e • GlobalTheory.LatVac.finTens 1 γ₀ - r') +
        (1 - (e + cA D e)) • GlobalTheory.LatVac.finTens 1 γ₀ + 2 • l (r, r') := by
      simp only [sub_smul, add_smul, one_smul]; abel
    rw [e3]
    exact add_mem (add_mem (add_mem hrΛ hrΛ') (hoff _ hv)) (nsmul_mem (hγl _ hp).1 2)
  have hsum := GlobalTheory.ThetaInter.inter_eq_sum_reps (HV sc) (alV D.host.d sc) A₁ A₂ (herm_HV sc) hsd hα₁ hα₂ (R ×ˢ R')
    (fun p => embH (tauE D) δ (toHom S T hS hT (γ p))) hz₂ hinj hsurj _ hfix₁

  have hF : xiN θ S T hS hT δ sc (om (s, s') f) =
      ((splitFacO μ μ x₀ y₀ : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) •
      ∑ p ∈ R ×ˢ R', alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) •
        Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc f) := by
    rw [hmain, xiN_smul, ← Finset.sum_product', xiN_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hpf p hp, xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hf.2.theta _ _ (hfo _),
      hph p hp]
  funext w
  rw [hF, hsum w]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, splitFacO, Circle.coe_mul, Circle.coe_inv,
    Finset.card_product, Nat.cast_mul]
  ring

end GlobalTheory.AdForm.SplitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one' : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem sec_mul' (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idlU_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul' q x y
  rw [h, sec_one'] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idlU (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idlU_mul q _ _ x.mul_inv, idlU_mul q _ _ x.inv_mul⟩

theorem continuous_idlU : Continuous (idlU q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem res_eq_locK {PP : Formalism.L2.DIV.Pl D.host.E} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hr : Formalism.IndefR.Links.IsRes H PP c) {a : D.host.E} (ha : IntAt PP a)
    (ha0 : a ≠ 0) (r : (Formalism.L2.DIV.kP PP)ˣ) (hra : (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a) :
    c r = H.locK PP (Units.mk0 a ha0) := by
  obtain ⟨r₀, s, hs, e⟩ := ha
  have hs0 : (algebraMap (𝓞 D.host.E) D.host.E s) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsp := Formalism.L2.Col.reduction_spec PP hs e
  have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
  have h2 := hr r₀ (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu * r) (by simp [e])
    (by simp [hra, hsp])
  rw [map_mul, map_mul, h1] at h2
  exact mul_left_cancel h2

end Place
end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem chi_idlU_rat {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle}
    {H : Formalism.L2.Host.HChar D.host.E} (hχ : Formalism.IndefR.Links.ChrEq χ H) {a : D.host.E} (ha0 : a ≠ 0) (u : kˣ)
    (hu : (u : k) = (ofSplit q).pr a) : (χ (idlU q u) : ℂ) = H.locK PP (Units.mk0 a ha0) := by
  exact hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idlU q u) (by
        change q.sec u + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hu]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)

end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)
section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

def prOU : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prOU_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prOU q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prOU q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prOU q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prOU_le {PP : Formalism.L2.DIV.Pl D.host.E} (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x)
    (z : 𝓞 D.host.E) : valuation k (prOU q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 ((hi _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

end Place

theorem tame_and_res : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  intro D k _ _ _ _ q PP h hi hd χ H c μ hχ hr hμ
  have comp : ∀ x : kˣ, (μ x : ℂ) = χ (idlU q x) := fun x => hμ x (idlU q x) rfl
  have val : ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), IntAt PP a →
      (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
    intro a u r ha hra hu
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA D)).map_zero)
    apply Units.ext
    rw [comp u, chi_idlU_rat q h hχ ha0 u hu, res_eq_locK hr ha ha0 r hra]
  refine ⟨?_, val⟩
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 →
      χ (idlU q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    have ha : IntAt PP a := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have hred : Formalism.L2.Col.redP PP a = 1 := by
      obtain ⟨r₀, s, hs, e⟩ := ha
      have hsp := Formalism.L2.Col.reduction_spec PP hs e
      have e' : prOU q s * y = prOU q r₀ := by
        rw [hy]
        exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
      have hrs : r₀ - s ∈ PP.asIdeal := by
        rw [prOU_lt q h, map_sub, ← e', ← mul_sub_one, map_mul]
        calc valuation k (prOU q s) * valuation k ((y : k) - 1) ≤ 1 * valuation k ((y : k) - 1) :=
              by gcongr; exact prOU_le q hi s
          _ < 1 := by rwa [one_mul]
      haveI := PP.isMaximal
      letI := Ideal.Quotient.field PP.asIdeal
      have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have e2 : Ideal.Quotient.mk PP.asIdeal r₀ = Ideal.Quotient.mk PP.asIdeal s :=
        Ideal.Quotient.eq.2 hrs
      rw [e2] at hsp
      exact mul_left_cancel₀ hu (hsp.trans (mul_one _).symm)
    have h1 := val a y 1 ha (by rw [Units.val_one, hred]) hy
    rw [map_one] at h1
    have h2 := comp y
    rw [h1, Units.val_one] at h2
    exact Circle.coe_injective h2.symm
  intro x hx
  suffices hs : χ (idlU q x) = 1 by
    apply Units.ext
    rw [comp x, hs]
    simp
  by_contra hne
  have hc : Continuous fun y => χ (idlU q y) := hχ.1.1.comp (continuous_idlU q)
  have h1 : {y : kˣ | χ (idlU q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

end GlobalTheory.LocMod.SplitHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPair_definite_place_character_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  first | exact @GlobalTheory.DownPair.pair_data | exact GlobalTheory.DownPair.pair_data | (intros; apply GlobalTheory.DownPair.pair_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TensorSrc

theorem op_prod {X Y : Type} (L : Module.End ℂ (X → ℂ)) (M : Module.End ℂ (Y → ℂ)) (f : X → ℂ) (g : Y → ℂ) (u : X)
    (v : Y) : L (fun u' => M (fun v' => f u' * g v') v) u = L f u * M g v := by
  have h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u' := by
    intro u'
    have : (fun v' => f u' * g v') = f u' • g := by funext v'; simp
    rw [this, map_smul]; simp [mul_comm]
  have h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f := by
    funext u'; simp [h1]
  rw [h2, map_smul]; simp [mul_comm]

theorem tensorSource : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorSource ψ d T := by
  intro D ψ hψ S A B d T
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T d
  have hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v := by
    intro fA fB u v
    simp [OrthDec.boxS]
  refine ⟨h1, h2, h3, h4, GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span D ψ hψ S A B T d, ?_, ?_⟩
  · intro χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB
    funext x
    obtain ⟨⟨u, v⟩, rfl⟩ := (d.resS T).symm.surjective x
    rw [GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]
    simp only [hb]
    exact op_prod _ _ fA fB u v
  · intro χA χB χT omS omA omB hS hA hB a b h f hf v
    refine ⟨?_, fun u => GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩
    have := (h4 _ ((GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v
    simpa using this

end GlobalTheory.TensorSrc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_datum_laws_under_levels : ∀ D : D7, LevelLawQ D := by
  first | exact @GlobalTheory.ChainTw.TwLaw.levelLawQ | exact GlobalTheory.ChainTw.TwLaw.levelLawQ | (intros; apply GlobalTheory.ChainTw.TwLaw.levelLawQ <;> assumption)
end

