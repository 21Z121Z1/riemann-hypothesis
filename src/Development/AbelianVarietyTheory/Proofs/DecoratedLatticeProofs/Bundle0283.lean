import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
section
noncomputable section

namespace GlobalTheory.LowJoin

section Normal
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ}

theorem adapted_of_normal (hϖ : valuation k (ϖ : k) = uniformizer k) (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
    (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x) (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
    {M : ℕ} (hM : s + 1 ≤ M) {g : GL (X s ⊕ Fin (0 + 1)) k} (hg : IsNormalRep T ϖ s 0 rfl g)
    (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) :
    (T.Psi g x₀ y ≠ 0 → y ∈ box _ (ϖ ^ M)⁻¹) ∧ ∀ z ∈ box _ (ϖ ^ M), T.Psi g x₀ (y + z) = T.Psi g x₀ y := by
  have wc : ∀ (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (v : X s ⊕ Fin (0 + 1) → k) r,
      (withCol x₀ y *ᵥ v) (.inl r) = (x₀ *ᵥ fun l => v (.inl l)) r + y r * v (.inr 0) := fun x₀ y v r => by
    simp [withCol, mulVec, dotProduct, Fintype.sum_sum_type]
  obtain ⟨e, z, he, hz, hl⟩ := hg
  rw [lat_bas hb] at hl
  have hbox : ∀ w : X (s + 1) → k, w ∈ box _ (ϖ ^ M) ↔ ∀ i, w i ∈ powInt ϖ M := fun w => by
    simp [mem_box, mem_pow]
  refine ⟨fun hy i => ?_, fun w hw => ?_⟩
  · have h1 := om_supp (hs _ _ _) g 1 _ hy
    rw [hl] at h1
    have h2 := mem_latOf_one.1 (h1 (Sum.elim 0 fun _ => 1) (mem_normal.2 ⟨fun r => by simpa using hz r,
      fun l => pow_mono hϖ (he l).2 (mem_pow_zero.2 (one_mem _))⟩)) (.inl i)
    rw [wc] at h2
    have h3 : y i ∈ 𝒪[k] := by simpa [show (fun _ : X s => (0 : k)) = 0 from rfl] using h2
    have := pow_mono hϖ (a := -(M : ℤ)) (by omega) (mem_pow_zero.2 h3)
    rw [mem_pow, _root_.zpow_neg, zpow_natCast] at this
    simpa using this
  · have h1 : withCol x₀ (y + w) = withCol x₀ y + (ϖ : k) • withCol 0 fun r => (ϖ : k) ^ (-1 : ℤ) * w r := by
      ext (r | r) (l | l) <;> simp [withCol]
    unfold Chain.Psi
    rw [h1]
    refine om_per hϖ (hp _ _ _) g 1 _ _ fun v hv => mem_latOf_one.2 ?_
    rintro (r | r)
    · rw [hl] at hv
      rw [wc, zero_mulVec, Pi.zero_apply, zero_add, mul_assoc, ← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
      exact pow_mono hϖ (by have := he 0; omega) (pow_mul_pow ((hbox w).1 hw r) ((mem_normal.1 hv).2 0))
    · exact r.elim0

theorem val_unif (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (h _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (h x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem continuous_of_cond {ψ : AddChar k Circle} (h : HasConductor ψ 1) : Continuous ψ := by
  have h0 : ∀ x ∈ (𝒪[k] : Set k), ψ x = 1 := fun x hx =>
    (h x).2 (by simpa [Valuation.mem_integer_iff] using hx) x le_rfl
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h1 : ∀ᶠ y in nhds x, ψ y = ψ x := by
    have h2 : (fun y => y - x) ⁻¹' (𝒪[k] : Set k) ∈ nhds x :=
      ((isOpen_int k).preimage (by fun_prop)).mem_nhds (by simp)
    filter_upwards [h2] with y hy
    rw [← sub_add_cancel y x, AddChar.map_add_eq_mul, h0 _ hy, one_mul]
  exact (continuousAt_const (y := ψ x)).congr (h1.mono fun _ e => e.symm)

end Normal

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S₀ : Set ℕ} {mu : Tup X.F X.E X.K S₀}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {s : ℕ}

abbrev Bdd (Pr : Primes X) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (γ : AutY X R j) : Prop :=
  ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
    ((qOf P : X.E) ^ j) • γ x ∈ lamYat (Pr := Pr) (R := R) j P

theorem exists_system {σ₀ : X.K →+* ℂ} {P : rowSG Pr sel mu} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : X.E →+* k} {W : TwData k} [MeasurableSpace k] [BorelSpace k] {ν : Measure k}
    (hν : IsUnitVol ν) (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hL : L.Ok Ch sel mu cst G s) (hI : IdxProd sel mu cst L)
    (hM : s + 1 ≤ cst.M) :
    ∃ A, (W.T s R).IsRepSystem A W.ψ ν ∧ (W.T s R).Adapted A (box _ (W.ϖ ^ cst.M)⁻¹) (box _ (W.ϖ ^ cst.M)) ∧
      (∀ j c h, Nonempty (L.β j) → A j c h = {g | ∃ b : L.β j, IsGL ι (L.h j b P) g}) ∧
      ∀ j c (h : j + 1 + c = s), Nonempty (L.β j) → (A (j + 1) c h).Nonempty →
        ∃ γ : AutY X R (j + 1), Bdd Pr (j + 1) P.1 γ ∧ ∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  classical
  have hc := hL.cst_ok
  have hm : R.m = s + 2 := hA.steps
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hmaps := GlobalTheory.T.completion_representative_mem_previous_index_set X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI
  have hnorm := GlobalTheory.T.completion_representatives_normal_form_mod_unipotent X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI hmaps
  have honto := GlobalTheory.T.exists_rational_double_coset_representative_bounds X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI
  haveI := hν.1
  have hϖ := val_unif W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  obtain ⟨hs, hp, hJ⟩ := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) fun _ _ _ => rfl
  have ex : ∀ j c (h : j + c = s) (β : DoubleCoset.Quotient (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 :
      Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)) ((W.T s R).lev j (c + 1) (by omega)).J), ∃ g, DoubleCoset.mk _ _ g = β ∧
        ((∃ g₁, DoubleCoset.mk _ _ g₁ = β ∧ GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h g₁) →
          GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h g) := by
    intro j c h β
    by_cases H' : ∃ g₁, DoubleCoset.mk _ _ g₁ = β ∧ GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h g₁
    · obtain ⟨g, h1, h2⟩ := H'
      exact ⟨g, h1, fun _ => h2⟩
    · exact ⟨_, DoubleCoset.out_eq' _ _ β, fun h' => absurd h' H'⟩
  choose σ σ1 σ2 using ex
  let A : RepFam k s (XIx (Fin R.k) (Fin R.t)) := fun j =>
    Nat.rec (motive := fun j => ∀ c, j + c = s → Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)) (fun _ _ => {1})
      (fun j B c h => if Nonempty (L.β (j + 1)) then {g | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g}
        else σ (j + 1) c h '' ⋃ g ∈ B (c + 1) (by omega), (W.T s R).idx W.ψ ν j c h g) j
  have hrat : ∀ j c h, Nonempty (L.β j) → A j c h = {g | ∃ b : L.β j, IsGL ι (L.h j b P) g} := by
    rintro (_ | j) c h hne
    · exact (GlobalTheory.T.firstStep_completionRepresentatives_eq_one X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI c h).symm
    · exact if_pos hne
  have hneg : ∀ j c (h : j + 1 + c = s), ¬ Nonempty (L.β (j + 1)) →
      A (j + 1) c h = σ (j + 1) c h '' ⋃ g ∈ A j (c + 1) (by omega), (W.T s R).idx W.ψ ν j c h g := fun j c h hne => if_neg hne
  have hsys : (W.T s R).IsRepSystem A W.ψ ν := by
    refine ⟨fun _ _ => rfl, fun j c h => ?_⟩
    by_cases hne : Nonempty (L.β (j + 1))
    · have hne' : Nonempty (L.β j) := ⟨(hL.nonvan j (by omega) hne.some P).choose⟩
      rw [hrat _ _ _ hne, hrat _ _ _ hne']
      refine ⟨?_, GlobalTheory.T.eq_of_same_doubleCoset_completion_rowRepresentatives X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI j c h, ?_⟩
      · rintro g' ⟨b, hb⟩
        obtain ⟨al, g, hg, hf⟩ := hmaps j c h b g' hb
        exact Set.mem_iUnion₂.2 ⟨g, ⟨al, hg⟩, g', rfl, hf⟩
      · intro β hβ
        obtain ⟨g, ⟨al, hg⟩, hβ⟩ := Set.mem_iUnion₂.1 hβ
        obtain ⟨h', rfl, hf⟩ := hβ
        obtain ⟨γ, ⟨g', hg', hdc⟩, hbd, hE⟩ := honto j c h al g hg (hnorm j (c + 1) (by omega) al g hg) h' hf
        obtain ⟨b, hb⟩ := GlobalTheory.T.exists_twistIndex_representative_of_bounds X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL hI j c h γ hbd ⟨al, hE⟩ hne
        obtain ⟨g'', hg'', -⟩ := GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut X R k ι (j + 1) (c + 1) (by simp only [cOf]; omega) (L.h (j + 1) b P)
        refine ⟨g'', ⟨b, hg''⟩, ?_⟩
        rw [← hdc]
        exact ((hLev (j + 1) (c + 1) (by omega) (L.h (j + 1) b P) g'' hg'').2.2 (by omega) γ g' hg').1 hb
    · rw [hneg j c h hne]
      refine ⟨?_, ?_, fun β hβ => ⟨_, ⟨β, hβ, rfl⟩, σ1 _ _ _ β⟩⟩
      · rintro _ ⟨β, hβ, rfl⟩
        exact (σ1 _ _ _ β).symm ▸ hβ
      · rintro _ ⟨β, -, rfl⟩ _ ⟨β', -, rfl⟩ e
        exact congrArg _ ((σ1 _ _ _ β).symm.trans (e.trans (σ1 _ _ _ β')))
  refine ⟨A, hsys, fun g hg => ?_, hrat, fun j c h hne ⟨g', hg'⟩ => ?_⟩
  · by_cases hne : Nonempty (L.β s)
    · rw [hrat _ _ _ hne] at hg
      obtain ⟨al, hg⟩ := hg
      exact ((GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA L G hL).1 al g hg).1
    · refine adapted_of_normal hϖ hb hs hp hM ?_
      obtain ⟨r, hr, hn⟩ := GlobalTheory.LatClass.exists_normal hϖ W.cond hb hs hp hJ hsys s 0 rfl g hg
      have key : ∀ j c h, ¬ Nonempty (L.β j) → ∀ g ∈ A j c h, ∃ β, g = σ j c h β := by
        rintro (_ | j) c h hne g hg
        · exact absurd ⟨hL.zero_uniq.choose⟩ hne
        · rw [hneg j c h hne] at hg
          obtain ⟨β, -, rfl⟩ := hg
          exact ⟨β, rfl⟩
      obtain ⟨β, rfl⟩ := key s 0 rfl hne g hg
      exact σ2 _ _ _ β ⟨_, ((DoubleCoset.eq _ _ _ _).2 ⟨r, hr, 1, one_mem _, (mul_one _).symm⟩).symm.trans (σ1 _ _ _ β), hn⟩
  · obtain ⟨g, hg, h', -, hf⟩ := Set.mem_iUnion₂.1 ((hsys.bij j c h).mapsTo hg')
    rw [hrat _ _ _ hne] at hg
    obtain ⟨al, hg⟩ := hg
    obtain ⟨γ, -, hbd, hE⟩ := honto j c h al g hg (hnorm j (c + 1) (by omega) al g hg) h' hf
    exact ⟨γ, hbd, al, hE⟩

theorem idx_succ (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel) (hs : cst.sharp = true) (hL : L.Ok Ch sel mu cst G s)
    {j : ℕ} (hj : j < s) (hne : Nonempty (L.β j))
    (h : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ γ : AutY X R (j + 1), Bdd Pr (j + 1) P.1 γ ∧ ∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) :
    Nonempty (L.β (j + 1)) := by
  classical
  choose γ h1 h2 using h
  obtain ⟨al⟩ := hne
  have hB := clL_base hL hX hPr hCh hs
  obtain ⟨b, -⟩ := hL.surj j hj (fun P => if hP : P.1 ∈ Pr.vGs then 1 else γ P hP)
    (fun P hP => by rw [dif_pos hP]; exact one_mem _) (fun P hP => by rw [dif_neg hP]; exact h1 P hP) (fun P => by
      by_cases hP : P.1 ∈ Pr.vGs
      · rw [dif_pos hP]
        exact ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G s hX hPr hCh hsel hs hL j hj P hP _ _ (hL.stabG j al P hP) (one_mem _)
          (by rw [hs]; exact GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.cosetOne hX hPr hCh hsel hs hL j (by omega) al P hP)).2
          (twNonVanG G.σ₀ hB hj P hP)⟩
      · rw [dif_neg hP]
        exact h2 P hP)
  exact ⟨b⟩

theorem isGL_unique {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : X.E →+* k} {j c : ℕ}
    {γ γ' : AutY X R j} {g g' : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k} (h : IsGL ι γ g) (h' : IsGL ι γ' g') : γ = γ' ↔ g = g' := by
  obtain ⟨e, he, hg⟩ := h
  obtain ⟨e', he', hg'⟩ := h'
  obtain rfl : e' = e := Equiv.ext fun r => Fin.ext ((he' r).trans (he r).symm)
  refine ⟨fun h => Units.ext (by rw [hg, hg', h]), fun h => ?_⟩
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun _ _).ext fun b => funext fun a => ι.injective ?_)
  have := congrFun (congrFun (hg.symm.trans (h ▸ hg')) (e'.symm a)) (e'.symm b)
  simpa [GlobalTheory.SymBridge.toLoc] using this

theorem exists_bij (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel) (hs : cst.sharp = true) (hL : L.Ok Ch sel mu cst G s)
    (hprod : IdxIsProd sel mu s L) (hone : ∀ j b (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1)
    {T : Type} (P : T → rowSG Pr sel mu) (hinj : Function.Injective P) (hoff : ∀ i, (P i).1 ∉ Pr.vGs)
    (hall : ∀ Q : rowSG Pr sel mu, Q.1 ∉ Pr.vGs → ∃ i, P i = Q)
    (C : T → ℕ → Type) (Rel : ∀ i j, AutY X R j → C i j → Prop)
    (ha : ∀ i j, j ≤ s → ∀ b : L.β j, ∃ y, Rel i j (L.h j b (P i)) y)
    (hb : ∀ i j, j ≤ s → Nonempty (L.β j) → ∀ y, ∃ b, Rel i j (L.h j b (P i)) y)
    (hc : ∀ i j, j ≤ s → ∀ γ γ' y y', Rel i j γ y → Rel i j γ' y' → (γ = γ' ↔ y = y'))
    (hd : ∀ i j, j < s → Nonempty (L.β j) → Nonempty (C i (j + 1)) →
      ∃ γ : AutY X R (j + 1), Bdd Pr (j + 1) (P i).1 γ ∧ ∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j (P i) (L.h j al (P i)) γ)
    (he : ∀ i j, j < s → Nonempty (C i (j + 1)) → Nonempty (C i j)) (j : ℕ) (hj : j ≤ s) :
    ∃ φ : L.β j → ∀ i, C i j, Function.Bijective φ ∧ ∀ b i, Rel i j (L.h j b (P i)) (φ b i) := by
  classical
  have hne : ∀ j, j ≤ s → (∀ i, Nonempty (C i j)) → Nonempty (L.β j) := by
    intro j
    induction j with
    | zero => exact fun _ _ => ⟨hL.zero_uniq.choose⟩
    | succ j ih =>
      intro hj h
      have h1 := ih (by omega) fun i => he i j hj (h i)
      refine idx_succ hX hPr hCh hsel hs hL hj h1 fun Q hQ => ?_
      obtain ⟨i, rfl⟩ := hall Q hQ
      exact hd i j hj h1 (h i)
  choose φ hφ using fun b i => ha i j hj b
  refine ⟨φ, ⟨fun b b' e => ?_, fun y => ?_⟩, hφ⟩
  · refine ((hprod j hj (L.h j b) fun Q => ⟨b, rfl⟩).unique (fun _ => rfl) fun Q => ?_)
    by_cases hQ : Q.1 ∈ Pr.vGs
    · rw [hone j b Q hQ, hone j b' Q hQ]
    · obtain ⟨i, rfl⟩ := hall Q hQ
      exact ((hc i j hj _ _ _ _ (hφ b i) (hφ b' i)).2 (congrFun e i)).symm
  · have h0 := hne j hj fun i => ⟨y i⟩
    choose b hb' using fun i => hb i j hj h0 (y i)
    let hh : rowSG Pr sel mu → AutY X R j := fun Q => if h : ∃ i, P i = Q then L.h j (b h.choose) Q else 1
    have h1 : ∀ i, hh (P i) = L.h j (b i) (P i) := fun i => by
      have h : ∃ i', P i' = P i := ⟨i, rfl⟩
      simp only [hh]
      rw [dif_pos h, hinj h.choose_spec]
    obtain ⟨b₀, h2, -⟩ := hprod j hj hh fun Q => by
      by_cases h : ∃ i, P i = Q
      · exact ⟨b h.choose, by simp only [hh]; rw [dif_pos h]⟩
      · exact ⟨h0.some, by simp only [hh]; rw [dif_neg h]; exact hone j _ Q (by_contra fun hQ => h (hall Q hQ))⟩
    exact ⟨b₀, funext fun i => (hc i j hj _ _ _ _ (hφ b₀ i) (hb' i)).1 ((h2 _).trans (h1 i))⟩

end GlobalTheory.LowJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ErrorExponentStatement
section
open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.MixPer GlobalTheory.MixModel MeasureTheory
  GlobalTheory.Core.Mi GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding Formalism.L2.SG.InstExistsPf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Matrix

noncomputable section

namespace GlobalTheory.Core.Mi.PerCmp

theorem exists_castE {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = instOf D) :
    ∃ ιE : I.E ≃+* D.host.E, ∀ y, ιE y ≍ y := by
  subst h; exact ⟨RingEquiv.refl _, fun _ => HEq.rfl⟩

theorem crdY_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = instOf D) (ιE : I.E ≃+* D.host.E)
    (hι : ∀ y, ιE y ≍ y) (hr : (D.sp.Y 0).rank = I.n) (x : Fin I.n → I.E) :
    crdY h x = fun k => ιE (x (Fin.cast hr k)) := by
  subst h; funext k; exact (eq_of_heq (hι _)).symm

structure Scaled {D : D7} (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word)
    {V₀ A L : HSp D} (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (lam : D.host.E) : Prop where
  ne : lam ≠ 0
  e_eq : d.e = Matrix.of fun k (a : Fin D.R.rS) => lam ^ (D.R.rS - (a : ℕ)) * crdY h (X.eR a) k
  f_eq : d.e' = Matrix.of fun k (a : Fin D.R.rS) =>
    (star (lam ^ (D.R.rS - (a : ℕ))))⁻¹ * crdY h (X.fR a) k
  line : IsLineVec L ζ
  z_eq : d.i₀.mulVec (vecB o ζ) = crdY h (X.zR u)

variable {D : D7} {X : HidaSetting.HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word}
  {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L}
  {ζ : Fin L.rank → D.host.E} {lam : D.host.E}

theorem hyp_linIndep {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    LinearIndependent D.host.E d.e.transpose := by
  have h1 : Function.Injective d.e.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (d.e'.conjTranspose * HSpace.gram S).mulVec v) hxy
    simpa [Matrix.mulVec_mulVec, d.e'e] using this
  exact Matrix.mulVec_injective_iff.mp h1

theorem hyp_e_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.e.conjTranspose * HSpace.gram S * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  simpa [Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.mul_assoc] using this

theorem Scaled.tieψ (hS : Scaled X h u d o ζ lam) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {θ : D.host.E} (hθ : θ * lam⁻¹ = thetaS D) (n : GA D (D.sp.Y 0)) :
    star (psiBes ψ d θ (vecB o ζ) n) =
      X.psiInfU u ((RowsJoinPinned.iotaX X h) n).1 * X.psiFinU u ((RowsJoinPinned.iotaX X h) n).2 := by
  obtain ⟨ιE, hι⟩ := exists_castE h
  have hr := rank_eq X h
  have hA := GlobalTheory.Core.TieSign.simpleSum_eq D d (fun a => crdY h (X.eR a)) (fun a => crdY h (X.fR a))
    (crdY h (X.zR u)) (vecB o ζ) 1 lam one_ne_zero hS.ne (by simp only [one_mul]; exact hS.e_eq)
    (by simp only [one_mul]; exact hS.f_eq) (by rw [one_smul]; exact hS.z_eq) n
  have hc := GlobalTheory.Core.TieSign.core D ψ hψ X.B.I h ιE hι hr X.psiEf X.psiEf_add X.psiEf_int
    X.psiEf_rat X.B.g (Pf.modulus_g_ne_zero X) X.eR X.fR (X.zR u) n
  have e1 : (fun a => crdY h (X.eR a)) = fun a k => ιE (X.eR a (Fin.cast hr k)) :=
    funext fun a => crdY_eq h ιE hι hr _
  have e2 : ∀ a, crdY h (X.fR a) = fun k => ιE (X.fR a (Fin.cast hr k)) :=
    fun a => crdY_eq h ιE hι hr _
  rw [e1, crdY_eq h ιE hι hr (X.zR u), Finset.sum_congr rfl fun a _ => by rw [e2 a]] at hA
  have hg : θ * lam⁻¹ = ((X.B.g : ℕ) : D.host.E)⁻¹ := by
    rw [hθ, thetaS, X.g_eq, one_div]
  rw [psiBes, hA, ← mul_assoc, ← map_mul, hg]
  exact hc

structure Match {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A)
    (hF : IsFrame X h u d o ζ) (ψ₀ : AddChar (AF ↥D.host.F) ℂ) (ν : Measure (flagN d))
    (𝓝 : Set (flagN d)) : Prop where
  emb : embA B.d B.o = embA d o
  per : ∀ φ f, B.lev.per ψ φ f = besPer ψ₀ (thetaS D) d o ζ B.vA.μ B.vA.𝓕 ν 𝓝 φ f

def scaleCols {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : Fin ρ → D.host.E)
    (hc : ∀ a, c a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * Matrix.diagonal c
  e' := d.e' * Matrix.diagonal fun a => (star (c a))⁻¹
  i₀ := d.i₀
  ee := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e, d.ee, Matrix.zero_mul, Matrix.mul_zero]
  e'e' := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e', d.e'e', Matrix.zero_mul, Matrix.mul_zero]
  e'e := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e, d.e'e, Matrix.one_mul, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, star_star]
    exact inv_mul_cancel₀ (hc a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

def IdentLev {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A) (Y : Full.Full X) (c : ℂ) : Prop :=
  ∀ (T : PoincareSetting.Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : RowDict.L2X X), RowFun X f →
    (φ : X.B.I.GA → ℂ) =ᵐ[RowDict.muX X] f →
      inner ℂ (star φ) (PoincareSetting.PuFun X u Y.hK (Y.Dt u) T) =
        c * ∫ y, B.lev.per ψ (B.colForm T (X.Wu u y))
          (fun g => f (RowsJoinPinned.iotaX X h g * (y, X.xu u))) ∂X.nuQ u

def IdentFrame (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (ψ : AddChar (AF ↥D.host.F) ℂ)
    (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
    (Dt : Set X.B.I.GA) (c : ℂ) : Prop :=
  ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
    ∀ φ : X.B.I.L2 X.B.μf X.B.fund,
      ((φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] fun x => star (f x)) →
        inner ℂ φ (PoincareSetting.PuFun X u hK Dt T) =
          c * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂X.nuQ u

def FrameLaw (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (A : HSp D) (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA)
    (C : Set ℂ) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
        ∃ c ∈ C, IdentFrame hF hK ψ μ 𝓕 ν 𝓝 Dt c

def posReals : Set ℂ := {c | ∃ r : ℝ, 0 < r ∧ c = r}

theorem besPer_domN {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) {ψ : AddChar (AF ↥D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (θ : D.host.E) (μ 𝓕) (ν : Measure (flagN d)) (hν : ν.IsHaarMeasure) {𝓝 𝓝' : Set (flagN d)}
    (h𝓝 : IsFundamentalDomain (NFlagQ S d.e) 𝓝 ν) (h𝓝' : IsFundamentalDomain (NFlagQ S d.e) 𝓝' ν)
    (φ : GA D A → ℂ) (f : GA D S → ℂ) (hf : ∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) :
    besPer ψ θ d o ζ μ 𝓕 ν 𝓝 φ f = besPer ψ θ d o ζ μ 𝓕 ν 𝓝' φ f := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : Countable (NFlagQ S d.e) := by
    have hinj : Function.Injective
        (fun x : NFlagQ S d.e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  unfold besPer
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine h𝓝.setIntegral_eq h𝓝' fun γ n => ?_
  have hγ : ((γ : flagN d) : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 γ.2
  change besFun ψ θ d o ζ φ f a ((γ : flagN d) * n) = _
  simp only [besFun, Subgroup.coe_mul]
  rw [psiBes_mul d ψ θ _ γ.1.2 n.2, GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ _ hγ, one_mul,
    mul_assoc ((γ : flagN d) : GA D S), hf _ hγ]

theorem besPer_domA {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {𝓕 : Set (GA D B.A)} (h𝓕 : IsFundamentalDomain (GQ B.A) 𝓕 B.vA.μ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ B.vA.μ 𝓕 B.vN.ν B.vN.𝓝 φ f = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  exact h𝓕.setIntegral_eq B.vA.fund fun γ x => Shift.inner_left B ψ hψ φ f hφ hf γ.2 x

def withDom {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A) (𝓕 : Set (GA D A))
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 B.vA.μ) (𝓝 : Set (flagN B.d))
    (h𝓝 : GlobalTheory.Per.IsUnitN _ B.d.e B.vN.ν 𝓝) : SBes X h u ψ A :=
  { B with vA := ⟨B.vA.μ, 𝓕, B.vA.haar, h𝓕⟩, vN := ⟨B.vN.ν, 𝓝, h𝓝⟩ }

def ErrorExponentStatement (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (u : D.what₂.Word) (A : HSp D) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
      ∀ Dt : Set X.B.I.GA, PoincareSetting.IsReps X u Dt →
        ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
          Unfolds hF hK ψ μ 𝓕 ν 𝓝 T f Dt c

def Conv (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (u : D.what₂.Word) (A : HSp D) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
        ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
          (∀ y, AbsConv μ 𝓕 ν 𝓝 (perFun hF hK ψ T f y)) ∧
            Integrable (perAt hF hK ψ μ 𝓕 ν 𝓝 T f) (X.nuQ u)

end GlobalTheory.Core.Mi.PerCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocEmb

theorem exists_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y),
    ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧
      ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  intro D k _ _ _ _ q V Y _ _ F
  obtain ⟨h1, -, h3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (GlobalTheory.LocMod.ofSplit q)).1 V Y F
  choose f hf hu using h1
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => (hu (x * y) _ (h3 _ _ _ _ (hf x) (hf y))).symm
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  let gl : GL Y k →* GA D V := { toFun := f, map_one' := hone, map_mul' := hmul }
  let fr : GlobalTheory.FinPl.Frame q V Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun x => (hf x).1, fun x => (hf x).2⟩
  refine ⟨gl, GlobalTheory.FrameCont.continuous_gl D k q V Y fr, fun x => hf x, fun g x hs hm => hu x g ⟨hs, hm⟩⟩

end GlobalTheory.LocEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_combination_split_place_datum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  first | exact @GlobalTheory.LocComb.exists_comb | exact GlobalTheory.LocComb.exists_comb | (intros; apply GlobalTheory.LocComb.exists_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  first | exact @GlobalTheory.SBOfHalf.exists_sb_ext_eq | exact GlobalTheory.SBOfHalf.exists_sb_ext_eq | (intros; apply GlobalTheory.SBOfHalf.exists_sb_ext_eq <;> assumption)
end

