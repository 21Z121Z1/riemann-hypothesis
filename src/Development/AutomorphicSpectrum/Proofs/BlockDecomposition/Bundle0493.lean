import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0473
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0484
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CountClosedComm

theorem relIndex_ne_zero_of_cover {G : Type} [Group G] (M W : Subgroup G) (S : Set G) (hS : S.Finite)
    (h : ∀ w ∈ W, ∃ s ∈ S, s⁻¹ * w ∈ M) : M.relIndex W ≠ 0 := by
  have hfin : Finite S := hS.to_subtype
  choose φ hφ hφM using h
  let ψ : W ⧸ M.subgroupOf W → S := fun q => ⟨φ q.out q.out.2, hφ _ q.out.2⟩
  have hinj : Function.Injective ψ := by
    intro q q' hqq
    have e : φ q.out q.out.2 = φ q'.out q'.out.2 := congrArg Subtype.val hqq
    have a := hφM _ q.out.2
    have b := hφM _ q'.out.2
    rw [← e] at b
    have hm : (q.out)⁻¹ * q'.out ∈ M.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      have := M.mul_mem (M.inv_mem a) b
      simpa [mul_assoc] using this
    calc q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
      _ = QuotientGroup.mk q'.out := QuotientGroup.eq.2 hm
      _ = q' := QuotientGroup.out_eq' q'
  have : Finite (W ⧸ M.subgroupOf W) := Finite.of_injective ψ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem exists_pow_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (L : Subgroup G)
    (hL : IsOpen (L : Set G)) (t : G) (hc : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    ∃ k : ℕ, 0 < k ∧ t ^ k ∈ L :=
  _root_.Bl.FirstLemmaC.goal1 L hL t hc

theorem cover_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T)
    (hC : IsCompact C) (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    ∃ F : Finset G, (∀ f ∈ F, f ∈ T) ∧ ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ T ⊓ L, t = γ * f * m := by
  have hTC : IsCompact ((T : Set G) ∩ C) := hC.inter_left hTc
  obtain ⟨F, hF, hU⟩ := hTC.elim_nhds_subcover (fun z => {g | z⁻¹ * g ∈ (L : Set G)}) (fun z _ =>
    IsOpen.mem_nhds (hLo.preimage (continuous_const.mul continuous_id)) (by simp [L.one_mem]))
  refine ⟨F, fun f hf => (hF f hf).1, ?_⟩
  intro t ht
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  have hcT : c ∈ T := by
    have := T.mul_mem (T.inv_mem (hΓ hγ)) ht
    simpa using this
  obtain ⟨f, hf, hcf⟩ := Set.mem_iUnion₂.1 (hU ⟨hcT, hc⟩)
  exact ⟨γ, hγ, f, hf, f⁻¹ * c, ⟨T.mul_mem (T.inv_mem (hF f hf).1) hcT, hcf⟩, by group⟩

def powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ ∃ k : ℕ, 0 < k ∧ t ^ k ∈ M}
  mul_mem' := by
    rintro a b ⟨ha, k, hk, hak⟩ ⟨hb, l, hl, hbl⟩
    refine ⟨T.mul_mem ha hb, k * l, Nat.mul_pos hk hl, ?_⟩
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, pow_mul a, pow_mul' b]
    exact M.mul_mem (M.pow_mem hak _) (M.pow_mem hbl _)
  one_mem' := ⟨T.one_mem, 1, one_pos, by simp [M.one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, hak⟩
    exact ⟨T.inv_mem ha, k, hk, by rw [inv_pow]; exact M.inv_mem hak⟩

theorem le_powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hM : M ≤ T) : M ≤ powRad T M hcomm :=
  fun m hm => ⟨hM hm, 1, one_pos, by simpa using hm⟩

theorem cptPart_le_powRad {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T L : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hLo : IsOpen (L : Set G)) :
    cptPart T ≤ powRad T (T ⊓ L) hcomm := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  obtain ⟨k, hk, hkL⟩ := exists_pow_mem L hLo t hc
  exact ⟨ht, k, hk, T.pow_mem ht k, hkL⟩

theorem inf_le_cptPart' {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hL : IsCompact (L : Set G)) : T ⊓ L ≤ cptPart T := by
  intro t ht
  apply Subgroup.subset_closure
  refine ⟨ht.1, hL.of_isClosed_subset isClosed_closure ?_⟩
  exact closure_minimal (fun x hx => (Subgroup.zpowers_le.2 ht.2) hx) hL.isClosed

theorem isOfFinOrder_of_pow_mem {G : Type} [Group G] (Γ M : Subgroup G)
    (hfin : ((Γ : Set G) ∩ (M : Set G)).Finite) (γ : G) (hγ : γ ∈ Γ) (k : ℕ) (hk : 0 < k) (hkM : γ ^ k ∈ M) :
    IsOfFinOrder γ := by
  have h : IsOfFinOrder (γ ^ k) := by
    rw [← finite_powers]
    refine hfin.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨Γ.pow_mem (Γ.pow_mem hγ k) n, M.pow_mem hkM n⟩
  exact h.of_pow hk.ne'

theorem relIndex_ne_zero_of_torsion {G : Type} [Group G] (T M W Γ : Subgroup G)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hMT : M ≤ T) (hMW : M ≤ W) (hΓ : Γ ≤ T)
    (F : Finset G) (hF : ∀ f ∈ F, f ∈ T) (hWT : W ≤ T)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ M, t = γ * f * m)
    (Tor : Set G) (hTor : Tor.Finite) (hsub : ∀ σ ∈ Γ, σ ∈ W → σ ∈ Tor) : M.relIndex W ≠ 0 := by
  have hr : ∀ f : G, ∃ r : G, (∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m) →
      r ∈ W ∧ ∃ γ ∈ Γ, ∃ m ∈ M, r = γ * f * m := by
    intro f
    by_cases h : ∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m
    · obtain ⟨t, ht, hh⟩ := h
      exact ⟨t, fun _ => ⟨ht, hh⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine relIndex_ne_zero_of_cover M W (Set.image2 (fun f σ => r f * σ) (F : Set G) Tor)
    (Set.Finite.image2 _ F.finite_toSet hTor) ?_
  intro w hw
  obtain ⟨a, ha, f, hf, c, hc, rfl⟩ := hcov w (hWT hw)
  obtain ⟨hrW, d, hd, e, he, hrf⟩ := hr f ⟨_, hw, a, ha, c, hc, rfl⟩
  have hσT : d⁻¹ * a ∈ T := T.mul_mem (T.inv_mem (hΓ hd)) (hΓ ha)
  have hσΓ : d⁻¹ * a ∈ Γ := Γ.mul_mem (Γ.inv_mem hd) ha
  have h1 : (r f)⁻¹ * (a * f * c) = e⁻¹ * (d⁻¹ * a) * c := by
    have hb : f * (d⁻¹ * a) = (d⁻¹ * a) * f := hcomm _ (hF f hf) _ hσT
    have hb' : f⁻¹ * (d⁻¹ * a) * f = d⁻¹ * a := by rw [mul_assoc, ← hb]; group
    rw [hrf]
    calc (d * f * e)⁻¹ * (a * f * c) = e⁻¹ * (f⁻¹ * (d⁻¹ * a) * f) * c := by group
      _ = e⁻¹ * (d⁻¹ * a) * c := by rw [hb']
  have hσW : d⁻¹ * a ∈ W := by
    have h2 : d⁻¹ * a = e * ((r f)⁻¹ * (a * f * c)) * c⁻¹ := by rw [h1]; group
    rw [h2]
    exact W.mul_mem (W.mul_mem (hMW he) (W.mul_mem (W.inv_mem hrW) hw)) (W.inv_mem (hMW hc))
  refine ⟨r f * (d⁻¹ * a), ⟨f, hf, d⁻¹ * a, hsub _ hσΓ hσW, rfl⟩, ?_⟩
  have hcm : e⁻¹ * (d⁻¹ * a) = (d⁻¹ * a) * e⁻¹ := hcomm _ (T.inv_mem (hMT he)) _ hσT
  have h3 : (r f * (d⁻¹ * a))⁻¹ * (a * f * c) = e⁻¹ * c := by
    rw [_root_.mul_inv_rev, mul_assoc, h1, hcm]
    group
  rw [h3]
  exact M.mul_mem (M.inv_mem he) hc

theorem isCompact_inf {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hTc : IsClosed (T : Set G)) (hL : IsCompact (L : Set G)) : IsCompact ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact hL.inter_left hTc

theorem part {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (L T Γ : Subgroup G)
    (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hTc : IsClosed (T : Set G))
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (htor : {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite) :
    (T ⊓ L).relIndex (cptPart T) ≠ 0 ∧ Finite (Γ ⊓ cptPart T : Subgroup G) := by
  set M := T ⊓ L with hM
  have hMT : M ≤ T := inf_le_left
  have hsub : ∀ σ ∈ Γ, σ ∈ powRad T M hcomm → σ ∈ {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ} := by
    rintro σ hσ ⟨-, k, hk, hkM⟩
    exact ⟨hσ, isOfFinOrder_of_pow_mem Γ M (hfin _ (isCompact_inf T L hTc hLc)) σ hσ k hk hkM⟩
  have hle : cptPart T ≤ powRad T M hcomm := cptPart_le_powRad T L hcomm hLo
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  refine ⟨?_, ?_⟩
  · have hW : M.relIndex (powRad T M hcomm) ≠ 0 :=
      relIndex_ne_zero_of_torsion T M (powRad T M hcomm) Γ hcomm hMT (le_powRad T M hcomm hMT) hΓ F hF
        (fun _ h => h.1) hcovF _ htor hsub
    exact fun h0 => hW (Subgroup.relIndex_eq_zero_of_le_right hle h0)
  · have : ((Γ ⊓ cptPart T : Subgroup G) : Set G).Finite :=
      htor.subset fun σ hσ => hsub σ hσ.1 (hle hσ.2)
    exact this.to_subtype

theorem finite_doubleCoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  let φ : F → DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T) :=
    fun f => DoubleCoset.mk _ _ ⟨f.1, hF f.1 f.2⟩
  refine Finite.of_surjective φ fun q => ?_
  induction q using Quotient.inductionOn' with
  | h t =>
    obtain ⟨γ, hγ, f, hf, m, hm, ht⟩ := hcovF t.1 t.2
    refine ⟨⟨f, hf⟩, ?_⟩
    refine Quotient.sound' ?_
    rw [DoubleCoset.rel_iff]
    refine ⟨⟨γ, hΓ hγ⟩, ?_, ⟨m, hm.1⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 hγ
    · exact Subgroup.mem_subgroupOf.2 (inf_le_cptPart' T L hLc hm)
    · apply Subtype.ext
      simp [ht, mul_assoc]

theorem main : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K T Γ : Subgroup G) (C : Set G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → Γ ≤ T →
  IsCompact C → (∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) →
  (∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) → {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite →
  (∀ x : G, T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
    (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0) ∧
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∧
  Finite (Γ ⊓ cptPart T : Subgroup G) ∧
  Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T) (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  intro G _ _ _ _ K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor
  have hLo : ∀ x : G, IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (Homeomorph.mulRight x⁻¹ ∘ Homeomorph.mulLeft x) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this, Set.image_comp]
    exact (Homeomorph.mulRight x⁻¹).isOpenMap _ ((Homeomorph.mulLeft x).isOpenMap _ hKo)
  have hLc : ∀ x : G, IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (fun g => x * g * x⁻¹) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this]
    exact hKc.image (by fun_prop)
  refine ⟨fun x => ⟨inf_le_cptPart' T _ (hLc x), (part _ T Γ C (hLo x) (hLc x) hTc hcomm hΓ hC hcov hfin htor).1⟩,
    fun x => ?_, (part K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor).2,
    finite_doubleCoset K T Γ C hKo hKc hTc hΓ hC hcov⟩
  have : ((Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite := by
    rw [Subgroup.coe_inf]
    exact hfin _ (hLc x)
  exact this.to_subtype

end GlobalTheory.CompanionTheory.CountClosedComm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvHecke

theorem conv_isHecke : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
    IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧
      ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  intro H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂
  have hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y)) := by
    intro y l hl x
    show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
    have e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]
  have hlev := fun y =>
    GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin
  have hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 →
      ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    apply hy
    rw [hlev y]
    have hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0 := by
      intro p
      by_cases h : f₁ p.out = 0
      · simp [h]
      · simp [hcon _ h]
    simp [hz]
  refine ⟨⟨?_, ?_⟩, hnz⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (h₁.1.isCompact.mul h₂.1.isCompact) ?_
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := hnz y hy
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩
  · intro l hl x
    constructor
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      rw [hlev (l * x), hlev x]
      congr 1
      refine (finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans
        (finsum_congr fun p => ?_)
      set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw
      have hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L) := by
        rw [hw, QuotientGroup.out_eq']
        show ((l * p.out : H) : H ⧸ L) = l • p
        conv_rhs => rw [← QuotientGroup.out_eq' p]
        rfl
      have hm : (l * p.out)⁻¹ * w ∈ L := QuotientGroup.eq.1 hcl
      have hinv := hu (l * x) hm (l * p.out)
      have hmul : l * p.out * ((l * p.out)⁻¹ * w) = w := by group
      simp only [hmul] at hinv
      refine hinv.trans ?_
      have e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x := by group
      rw [e, (h₁.2 l hl _).1]
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      have e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x) := by
        funext z
        rw [← mul_assoc, (h₂.2 l hl _).2]
      rw [e]

end GlobalTheory.CompanionTheory.ConvHecke

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormulaStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_coset_formula : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSumStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_coset_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)), IsHeckeOp π J g T → ∀ (r : ℕ) (x : Fin r → GL (Fin N) k), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((T v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSplitRankOneStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_split_rank_one : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h → IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) → Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.hermSwap_struct | exact GlobalTheory.CompanionTheory.KFin.hermSwap_struct | (intros; apply GlobalTheory.CompanionTheory.KFin.hermSwap_struct <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianValuationSplitCriterionStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_valuation_split_criterion : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | exact GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even | (intros; apply GlobalTheory.CompanionTheory.KFin.EvenAniso.pair_mem_of_even <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintEqOfLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintSmaller

theorem hint_eq_of_le : ∀ {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ), S ≤ K → S ≤ rStab u →
    S.relIndex K ≠ 0 → (Function.support fun q : H ⧸ S => u q.out).Finite →
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ K S u hSK hSu hfin _
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K S u hSK hSu hfin

end GlobalTheory.CompanionTheory.HintSmaller
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsTer
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem link : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ), IsLTChar Bw.Kw χ →
    ∀ (φ : w.adicCompletion E →+* Om l), Continuous φ →
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
      art (localIdele E w x) = toAb E Ω σ →
      (((χ (Bw.e σ) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l) = φ (x : w.adicCompletion E) := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI art hart χ hχ φ hφ hφj x σ hx hσ hxσ
  letI algF : Algebra (w.adicCompletion E) (Om l) := φ.toAlgebra
  have hmap : ∀ y, algebraMap (w.adicCompletion E) (Om l) y = φ y := fun _ => rfl
  have hr : Set.range (algebraMap (w.adicCompletion E) (Om l)) = (Bw.Kw.1 : Set (Om l)) :=
    GlobalTheory.T.local_embedding_range_eq_field Bw w φ hφ hφj
  haveI hsep : IsSepClosure (w.adicCompletion E) (Om l) := GlobalTheory.T.is_sep_closure_of_range_eq Bw.Kw hr
  haveI hext : ValuativeExtension (w.adicCompletion E) (Om l) := ⟨fun a b => by
    rw [GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le]
    exact (GlobalTheory.T.valuation_le_iff_norm_embedding φ hφ a b).symm⟩
  haveI hclosed : IsSepClosed (Om l) := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI halg : Algebra.IsAlgebraic (w.adicCompletion E) (Om l) := hsep.separable.isAlgebraic
  obtain ⟨π, hπ, H⟩ := GlobalTheory.T.exists_uniformizer_galois_action hχ hr
  let g' := Bw.e σ
  have hfix : ∀ y, (g' : GQ l) (algebraMap (w.adicCompletion E) (Om l) y) = algebraMap (w.adicCompletion E) (Om l) y := by
    intro y
    have hy : algebraMap (w.adicCompletion E) (Om l) y ∈ Bw.Kw.1 := by
      have : algebraMap (w.adicCompletion E) (Om l) y ∈ (Bw.Kw.1 : Set (Om l)) := hr ▸ ⟨y, rfl⟩
      exact this
    exact g'.2 ⟨_, hy⟩
  let g : Om l ≃ₐ[w.adicCompletion E] Om l := { (g' : GQ l).toRingEquiv with commutes' := hfix }
  have hg : ∀ y, g y = (g' : GQ l) y := fun _ => rfl
  obtain ⟨u, hu, hact⟩ := H g g' hg
  have hdeg : unramifiedDegree (w.adicCompletion E) (Om l) g = 1 := GlobalTheory.T.local_bridge_lubin_tate_field Bw hI σ hσ g hg
  have hloc := GlobalTheory.T.lubin_tate_unramified_degree_one hπ (isLubinTateSeries_ltPoly π) u g hdeg hact
  have hres := fun (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L] =>
    GlobalTheory.T.local_global_artin_compatible w Bw.j (fun y => (hφj y).symm) (unitsIncl _ u⁻¹) (σ : G E Ω) g
      (fun z => by rw [hg]; exact Bw.e_comm σ z) hloc L
  have h1 : art (localIdele E w (unitsIncl _ u)) = toAb E Ω σ := by
    rw [GlobalTheory.T.global_artin_map_unique art hart]
    have hb : ∀ a b : Gab E Ω, (∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
        PositivityTheory.FamInh.res L a = PositivityTheory.FamInh.res L b) → a = b := by
      intro a b h
      have := PositivityTheory.FamInh.mem_of_forall_res (H := ⊥) (g := a * b⁻¹) (by simpa using isClosed_singleton)
        fun L _ _ _ => by rw [map_mul, map_inv, h L, mul_inv_cancel]
      exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 this)
    refine hb _ _ fun L _ _ => ?_
    rw [hres L, MonoidHom.inv_apply, map_inv, map_inv]
    simp
  have h2 : unitsIncl _ u = x :=
    GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w (h1.trans hxσ.symm)
  rw [← hu, ← h2]
  rfl

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulusStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mulVec_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
  IsLocallyConstant F → HasCompactSupport F →
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
    ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kernel_compact_open : PositivityTheory.Rg.BcB.G8.KfOC := by
  first | exact @GlobalTheory.CompanionTheory.IntegralPoints.kfOC | exact GlobalTheory.CompanionTheory.IntegralPoints.kfOC | (intros; apply GlobalTheory.CompanionTheory.IntegralPoints.kfOC <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighestStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ R : H →ₗ[ℂ] V, (∀ a b w, R (G a b w) = D a b (R w)) → (∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) → R = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | exact GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | (intros; apply GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPickRealStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pick_real : PositivityTheory.RgBcC.RealD.InvPick := by
  first | exact @GlobalTheory.CompanionTheory.InvPickKP.invPick | exact GlobalTheory.CompanionTheory.InvPickKP.invPick | (intros; apply GlobalTheory.CompanionTheory.InvPickKP.invPick <;> assumption)
end

