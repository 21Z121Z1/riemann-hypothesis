import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0724
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReduction
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimateStatement
section
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluingStatement
section
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_gluing : Glue := by
  first | exact @GlobalTheory.CompanionTheory.PolyDenominator.glue | exact GlobalTheory.CompanionTheory.PolyDenominator.glue | (intros; apply GlobalTheory.CompanionTheory.PolyDenominator.glue <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiltrationStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_antitone_filtration_of_chain : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ) (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b → (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration | exact GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorEmbeddingsExist
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def localization₂ (a b : ℕ) (w : Pl E) : (GLw a w × GLw b w) →* Hf E a b :=
  (locGL E a w).prodMap (locGL E b w)

theorem continuous_locP (w : Pl E) : Continuous (localization₂ (E := E) a b w) :=
  ((GlobalTheory.EulerTw.continuous_locGL_spl E a w).comp continuous_fst).prodMk
    ((GlobalTheory.EulerTw.continuous_locGL_spl E b w).comp continuous_snd)

theorem atW_locP (w : Pl E) (m : GLw a w × GLw b w) : atW w (localization₂ a b w m) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

theorem component_localEmbedding_eq_one_of_ne {v w : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) : atW v (localization₂ a b w m) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

theorem pc_thF_of_one {n : ℕ} {v : Pl E} {x : GL (Fin n) (Af E)}
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x = 1) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = 1 := by
  refine (GlobalTheory.EulerTwU.pc_thF v x).trans ?_
  rw [h]
  exact (congrArg _ (map_one (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)))).trans (map_one _)

theorem component_conj_localEmbedding_eq_one_of_ne {v w : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    atW v (thP E a b (localization₂ a b w m)) = 1 := by
  exact Prod.ext (pc_thF_of_one (pLoc_locGL_of_ne h m.1)) (pc_thF_of_one (pLoc_locGL_of_ne h m.2))

def localEmb (a b : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b
  | .inl w => localization₂ a b w.1
  | .inr w => (thP E a b).comp (localization₂ a b w.1)

theorem continuous_factorEmb {S : Set (Pl E)} (i : Slot S) : Continuous (localEmb (E := E) a b i) := by
  rcases i with w | w
  · exact continuous_locP w.1
  · exact GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP.comp (continuous_locP w.1)

theorem cp_factorEmb {S : Set (Pl E)} (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : i.cp a b (localEmb a b i m) = m := by
  rcases i with w | w
  · exact atW_locP w.1 m
  · change atW w.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = m
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact atW_locP w.1 m

theorem cp_factorEmb_of_ne {S : Set (Pl E)} (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (hij : i ≠ j) :
    j.cp a b (localEmb a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inl (Subtype.ext h.symm))) m
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (h ▸ w.2)
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    refine GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 ?_
    have h' : GlobalTheory.EulerTw.cPl E v.1 = w.1 := h
    rw [← h', GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact v.2
  · change atW v.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = 1
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inr (Subtype.ext h.symm))) m

theorem finGL_thF (n : ℕ) (k : GL (Fin n) (Af E)) :
    finGL E n (thF E n k) = thetaGL n (conjAd E) (finGL E n k) :=
  (GlobalTheory.ThetaPull.thetaA_finGL k).symm

end GlobalTheory.CompanionTheory.FinActS

theorem GlobalTheory.CompanionTheory.FinActS.exists_factorEmb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  intro E _ _ _ a b S hS
  refine ⟨localEmb a b, continuous_factorEmb, cp_factorEmb, fun i j m h => cp_factorEmb_of_ne hS i j m h, fun w m => rfl, fun w m => ?_⟩
  exact Prod.ext (finGL_thF a _) (finGL_thF b _)

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLevelSubgroupsExist
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.PositionTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem eventually_factor {S : Set (Pl E)} {P : Slot S → Prop}
    (h₁ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S, P (Sum.inl ⟨w, hw⟩))
    (h₂ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S ∧ IsSplitAt w, P (Sum.inr ⟨w, hw⟩)) :
    ∀ᶠ i : Slot S in cofinite, P i := by
  have f₁ := Filter.eventually_cofinite.1 h₁
  have f₂ := Filter.eventually_cofinite.1 h₂
  refine Filter.eventually_cofinite.2 ?_
  refine (((f₁.preimage (Subtype.val_injective (p := fun w => w ∈ S)).injOn).image Sum.inl).union
    ((f₂.preimage (Subtype.val_injective (p := fun w => w ∈ S ∧ IsSplitAt w)).injOn).image Sum.inr)).subset ?_
  rintro (⟨w, hw⟩ | ⟨w, hw⟩) hi
  · exact Or.inl ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩
  · exact Or.inr ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩

def localLevel {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem exists_factor_level₂ {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, o₁, e₁, i₁⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₂
  have c₁ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁
  have c₂ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂
  refine ⟨localLevel L₁ L₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | w)
    · exact o₁ w.1
    · exact o₂ w.1
  · exact eventually_factor (e₁.mono fun w h _ => h) (e₂.mono fun w h _ => h)
  · rintro (w | w) k hk x
    · exact (i₁ w.1 k hk x).2
    · exact (i₂ w.1 k hk x).2
  · rintro (w | w)
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₁ w.1
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₂ w.1
  · exact eventually_factor (c₁.mono fun w h _ => h) (c₂.mono fun w h _ => h)

end GlobalTheory.CompanionTheory.PositionTest

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictedProductQuotient
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem finite_cosets_of_components_mem
    {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i)
    (V : ∀ i, Subgroup (Hl i)) (Q : ∀ i, Set (Hl i))
    (hQ : ∀ i, ∀ x ∈ Q i, ∀ u ∈ V i, x * u ∈ Q i)
    (hQf : ∀ i, {q : Hl i ⧸ V i | q.out ∈ Q i}.Finite)
    (hQV : ∀ᶠ i in cofinite, Q i ⊆ V i) :
    {q : Γ ⧸ (⨅ i, (V i).comap (p i)) | ∀ i, p i q.out ∈ Q i}.Finite := by
  have hT : {i | ¬ Q i ⊆ V i}.Finite := Filter.eventually_cofinite.mp hQV
  haveI : Finite {i | ¬ Q i ⊆ V i} := hT.to_subtype
  let f : Γ ⧸ (⨅ i, (V i).comap (p i)) → ∀ i : {i | ¬ Q i ⊆ V i}, Hl i.1 ⧸ V i.1 :=
    fun q i => ((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)
  have hfin : (Set.univ.pi fun i : {i | ¬ Q i ⊆ V i} =>
      {c : Hl i.1 ⧸ V i.1 | c.out ∈ Q i.1}).Finite :=
    Set.Finite.pi fun i => hQf i.1
  refine Set.Finite.of_injOn (f := f) ?_ ?_ hfin
  · intro q hq i _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V i.1) (p i.1 q.out)
    show (((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)).out ∈ Q i.1
    rw [hh]
    exact hQ i.1 _ (hq i.1) _ h.2
  · intro q hq q' hq' hfq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    refine Subgroup.mem_iInf.mpr fun i => ?_
    rw [Subgroup.mem_comap, map_mul, map_inv]
    by_cases hi : Q i ⊆ V i
    · exact (V i).mul_mem ((V i).inv_mem (hi (hq i))) (hi (hq' i))
    · exact QuotientGroup.eq.mp (congrFun hfq ⟨i, hi⟩)

end GlobalTheory.CompanionTheory.FinActS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSumFiberDecomposition
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS.SumFiber

theorem finsum_cosets_retraction {Γ H : Type} [Group Γ] [Group H] (p : Γ →* H) (e : H →* Γ)
    (hpe : ∀ m, p (e m) = m)
    (L : Subgroup Γ) (V : Subgroup H) (hLV : ∀ u ∈ L, p u ∈ V) (φ : Γ → ℂ)
    (hφ : ∀ u ∈ L, ∀ x, φ (x * u) = φ x) (hfin : {q : Γ ⧸ L | φ q.out ≠ 0}.Finite) :
    ∑ᶠ q : Γ ⧸ L, φ q.out =
      ∑ᶠ m : H ⧸ V, ∑ᶠ q : Γ ⧸ L,
        (V : Set H).indicator (1 : H → ℂ) (p q.out) * φ (e m.out * q.out) := by
  have outL : ∀ x : Γ, ∃ u ∈ L, (QuotientGroup.mk x : Γ ⧸ L).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul L x
    exact ⟨u, u.2, hu⟩
  have outV : ∀ x : H, ∃ u ∈ V, (QuotientGroup.mk x : H ⧸ V).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul V x
    exact ⟨u, u.2, hu⟩
  have hφout : ∀ x : Γ, φ (QuotientGroup.mk x : Γ ⧸ L).out = φ x := by
    intro x
    obtain ⟨u, hu, h⟩ := outL x
    rw [h, hφ u hu]
  let S : Set (Γ ⧸ L) := {q | p q.out ∈ V}
  have hS : ∀ x : Γ, p x ∈ V → (QuotientGroup.mk x : Γ ⧸ L) ∈ S := by
    intro x hx
    obtain ⟨u, hu, h⟩ := outL x
    change p (QuotientGroup.mk x : Γ ⧸ L).out ∈ V
    rw [h, map_mul]
    exact V.mul_mem hx (hLV u hu)
  let T : (H ⧸ V) × S → Γ ⧸ L := fun a => QuotientGroup.mk (e a.1.out * a.2.1.out)
  have hinj : Function.Injective T := by
    rintro ⟨m, q, hq⟩ ⟨m', q', hq'⟩ h
    have hq1 : p q.out ∈ V := hq
    have hq2 : p q'.out ∈ V := hq'
    have h1 : (e m.out * q.out)⁻¹ * (e m'.out * q'.out) ∈ L := QuotientGroup.eq.1 h
    have h2 := hLV _ h1
    simp only [map_mul, map_inv, hpe] at h2
    have hm : m = m' := by
      rw [← QuotientGroup.out_eq' m, ← QuotientGroup.out_eq' m']
      refine QuotientGroup.eq.2 ?_
      have h3 : m.out⁻¹ * m'.out
          = p q.out * ((p q.out)⁻¹ * m.out⁻¹ * (m'.out * p q'.out)) * (p q'.out)⁻¹ := by
        group
      rw [h3]
      refine V.mul_mem (V.mul_mem hq1 ?_) (V.inv_mem hq2)
      simpa [_root_.mul_inv_rev] using h2
    subst hm
    have hqq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      refine QuotientGroup.eq.2 ?_
      have h3 : q.out⁻¹ * q'.out = (e m.out * q.out)⁻¹ * (e m.out * q'.out) := by group
      rw [h3]
      exact h1
    subst hqq
    rfl
  have hsurj : Function.Surjective T := by
    intro q
    obtain ⟨v, hv, hm⟩ := outV (p q.out)
    let m : H ⧸ V := QuotientGroup.mk (p q.out)
    have hmem : p ((e m.out)⁻¹ * q.out) ∈ V := by
      have : p ((e m.out)⁻¹ * q.out) = v⁻¹ := by
        simp only [map_mul, map_inv, hpe, m]
        rw [hm]
        group
      rw [this]
      exact V.inv_mem hv
    refine ⟨(m, ⟨QuotientGroup.mk ((e m.out)⁻¹ * q.out), hS _ hmem⟩), ?_⟩
    obtain ⟨u, hu, h⟩ := outL ((e m.out)⁻¹ * q.out)
    change (QuotientGroup.mk (e m.out * (QuotientGroup.mk ((e m.out)⁻¹ * q.out) : Γ ⧸ L).out) :
      Γ ⧸ L) = q
    rw [h]
    refine Eq.trans (QuotientGroup.eq.2 ?_) (QuotientGroup.out_eq' q)
    have h3 : (e m.out * ((e m.out)⁻¹ * q.out * u))⁻¹ * q.out = u⁻¹ := by group
    rw [h3]
    exact L.inv_mem hu
  let E : (H ⧸ V) × S ≃ Γ ⧸ L := Equiv.ofBijective T ⟨hinj, hsurj⟩
  have hsupp : (Function.support
      (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out))).Finite := by
    refine (hfin.preimage (f := T) hinj.injOn).subset ?_
    intro a ha
    change φ (QuotientGroup.mk (e a.1.out * a.2.1.out) : Γ ⧸ L).out ≠ 0
    rw [hφout]
    exact ha
  calc ∑ᶠ q : Γ ⧸ L, φ q.out
      = ∑ᶠ a : (H ⧸ V) × S, φ (E a).out :=
        (finsum_comp_equiv E (f := fun q : Γ ⧸ L => φ q.out)).symm
    _ = ∑ᶠ a : (H ⧸ V) × S, φ (e a.1.out * a.2.1.out) :=
        finsum_congr fun a => hφout _
    _ = ∑ᶠ m : H ⧸ V, ∑ᶠ q : S, φ (e m.out * q.1.out) :=
        finsum_curry (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out)) hsupp
    _ = _ := by
        refine finsum_congr fun m => ?_
        rw [finsum_set_coe_eq_finsum_mem S (f := fun q : Γ ⧸ L => φ (e m.out * q.out)),
          finsum_mem_def]
        refine finsum_congr fun q => ?_
        by_cases hq : p q.out ∈ V
        · have hq' : q ∈ S := hq
          rw [Set.indicator_of_mem hq', Set.indicator_of_mem (show p q.out ∈ (V : Set H) from hq)]
          simp
        · have hq' : q ∉ S := hq
          rw [Set.indicator_of_notMem hq',
            Set.indicator_of_notMem (show p q.out ∉ (V : Set H) from hq)]
          simp

end GlobalTheory.CompanionTheory.FinActS.SumFiber
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProduct
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActS

theorem finprod_sum_split {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (h₁ : (Function.mulSupport fun x => f (Sum.inl x)).Finite)
    (h₂ : (Function.mulSupport fun x => f (Sum.inr x)).Finite) :
    ∏ᶠ i, f i = (∏ᶠ x, f (Sum.inl x)) * ∏ᶠ x, f (Sum.inr x) := by
  have hu : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext i; cases i <;> simp
  have e₁ : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₁.image Sum.inl).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have e₂ : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₂.image Sum.inr).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) :=
    Set.disjoint_left.2 (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; cases hy)
  rw [← finprod_mem_univ, hu, finprod_mem_union' hd e₁ e₂,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem finFn_eq_finprod_factor {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b) : finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  set g₁ : Pl E → ℂ := fun w => φ₁ w (atW w y) with hg₁
  set g₂ : Pl E → ℂ := fun w => if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg₂
  have o₁ : ∀ᶠ w in cofinite, g₁ w = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem y] with w e m
    have m' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    simp only [hg₁]
    rw [e, Set.indicator_of_mem m']
    simp
  have o₂ : ∀ᶠ w in cofinite, φ₂ w (atW w (thP E a b y)) = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂,
      (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem (thP E a b y)] with w e m
    have m' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    rw [e, Set.indicator_of_mem m']
    simp
  have f₁ : (Function.mulSupport g₁).Finite := eventually_cofinite.1 o₁
  have f₂' : (Function.mulSupport fun w => φ₂ w (atW w (thP E a b y))).Finite := eventually_cofinite.1 o₂
  have f₂ : (Function.mulSupport g₂).Finite := by
    refine f₂'.subset fun w hw => ?_
    by_cases hs : IsSplitAt w
    · simpa [hg₂, hs, Function.mem_mulSupport] using hw
    · exact absurd (by simp [hg₂, hs]) hw
  have l₁ : (Function.mulSupport fun x : {w // w ∈ S} => g₁ x.1).Finite :=
    (f₁.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have l₂ : (Function.mulSupport fun x : {w // w ∈ S ∧ IsSplitAt w} => φ₂ x.1 (atW x.1 (thP E a b y))).Finite :=
    (f₂'.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have hs : ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) =
      (∏ᶠ x : {w // w ∈ S}, g₁ x.1) * ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) :=
    finprod_sum_split (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) l₁ l₂
  have c₁ : ∏ᶠ x : {w // w ∈ S}, g₁ x.1 = ∏ᶠ w ∈ S, g₁ w :=
    finprod_subtype_eq_finprod_cond (f := g₁) (fun w => w ∈ S)
  have c₂ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ w ∈ S, g₂ w := by
    have e₀ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) =
        ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, g₂ x.1 :=
      finprod_congr fun x => by simp [hg₂, x.2.2]
    rw [e₀, finprod_subtype_eq_finprod_cond (f := g₂) (fun w => w ∈ S ∧ IsSplitAt w)]
    refine finprod_mem_inter_mulSupport_eq' g₂ {w | w ∈ S ∧ IsSplitAt w} S fun w hw => ?_
    have hsp : IsSplitAt w := by
      by_contra hn
      exact hw (by simp [hg₂, hn])
    exact ⟨fun h => h.1, fun h => ⟨h, hsp⟩⟩
  rw [hs, c₁, c₂]
  exact finprod_mem_mul_distrib' (f₁.subset Set.inter_subset_right) (f₂.subset Set.inter_subset_right)

end GlobalTheory.CompanionTheory.FinActS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReductionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_joint_reduction : PositivityTheory.SiegelWeilFormula.Gunr.JtLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrJt.jtLev | exact GlobalTheory.CompanionTheory.GunrJt.jtLev | (intros; apply GlobalTheory.CompanionTheory.GunrJt.jtLev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
end

