import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolveUnitriangular
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import GroundTheory.AutomorphicForms.WhittakerCriterion

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixedStatement
section
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_fixed : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  first | exact @GlobalTheory.CompanionTheory.RepTensor.contrFix | exact GlobalTheory.CompanionTheory.RepTensor.contrFix | (intros; apply GlobalTheory.CompanionTheory.RepTensor.contrFix <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTailStatement
section
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  first | exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | exact GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | (intros; apply GlobalTheory.CompanionTheory.IwahoriCount.cosetCount <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosieve_pairing_family_compat : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_gen | exact GlobalTheory.CompanionTheory.KunGlue.glue_gen | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleContra

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullForm (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ f.toLinearMap, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show σ.dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v => by
          have h : σ.dual g l.1 = l.1 := hg
          have h2 := LinearMap.congr_fun h (f v)
          have h3 : σ.dual g l.1 (f v) = l.1 (σ g⁻¹ (f v)) := rfl
          rw [h3, ← f.isIntertwining] at h2
          exact h2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem pullForm_injective (f : π.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (pullForm f) := fun a b h => Subtype.ext (LinearMap.ext fun y => by
  obtain ⟨v, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem mem_range_pullForm (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (l : smoothPart π.dual)
    (hl : ∀ v, f v = 0 → l.1 v = 0) : l ∈ (pullForm f).range := by
  let q : (V ⧸ LinearMap.ker f.toLinearMap) →ₗ[ℂ] ℂ := (LinearMap.ker f.toLinearMap).liftQ l.1 (fun v hv => hl v hv)
  let l' : Module.Dual ℂ W := q ∘ₗ (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl' : ∀ v, l' (f v) = l.1 v := fun v => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show q ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v)) = _
    rw [this]
    rfl
  have hs : l' ∈ smoothPart σ.dual := mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds l.2 (by
      show π.dual 1 l.1 = l.1
      rw [map_one]
      rfl)) fun g hg => LinearMap.ext fun w => by
      obtain ⟨v, rfl⟩ := hf w
      have h : π.dual g l.1 = l.1 := hg
      have h2 := LinearMap.congr_fun h v
      have h3 : π.dual g l.1 v = l.1 (π g⁻¹ v) := rfl
      rw [h3] at h2
      show l' (σ g⁻¹ (f v)) = l' (f v)
      rw [← f.isIntertwining, hl', hl', h2])
  exact ⟨⟨l', hs⟩, Subtype.ext (LinearMap.ext fun v => hl' v)⟩

theorem isSmooth_subContra (S : Subrepresentation (contra π)) : IsSmooth S.toRepresentation := fun l => by
  have : {g : G | S.toRepresentation g l = l} = {g : G | contra π g l.1 = l.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact isSmooth_contra π l.1

def evalForms (hπ : IsSmooth π) (S : Subrepresentation (contra π)) : π.IntertwiningMap (contra S.toRepresentation) where
  toLinearMap :=
    { toFun := fun v => ⟨{ toFun := fun l => l.1.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg =>
          LinearMap.ext fun l => by
            have h : π g v = v := hg
            show ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v = l.1.1 v
            rw [contra_apply, inv_inv, h])⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun l => map_add l.1.1 a b)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun l => map_smul l.1.1 c a) }
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun l => by
    show l.1.1 (π g v) = ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v
    rw [contra_apply, inv_inv])

end General

theorem isSocle_contra_of_isCosocle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  intro k _ _ _ _ hA N V W _ _ _ _ σ π hπ _ hc
  obtain ⟨hi, f, hf, hu⟩ := hc
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have hσ : IsSmooth σ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  have hci : (contra σ).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ hσ hi) hi
  refine ⟨hci, pullForm f, pullForm_injective f hf, fun S hS => ?_⟩
  have hSi := GlobalTheory.MaschkeForms.isIrreducible_of_isAtom hS
  have hcS : (contra S.toRepresentation).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (isSmooth_subContra S) hSi) hSi
  let e := evalForms hπ S
  have hr : e.range ≠ ⊥ := fun h0 => hS.1 (eq_bot_iff.2 fun l hl => by
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : e v ∈ (⊥ : Subrepresentation (contra S.toRepresentation)) := h0 ▸ ⟨v, rfl⟩
    have hv0 : e v = 0 := hv
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩)
  have he : Function.Surjective e := fun y => by
    have : y ∈ e.range := by
      have ht : e.range = ⊤ := (eq_bot_or_eq_top _).resolve_left hr
      rw [ht]
      trivial
    exact this
  have hk : e.ker = f.ker := hu _ (isCoatom_ker hcS e he)
  have hle : S ≤ (pullForm f).range := fun l hl => mem_range_pullForm f hf l fun v hv => by
    have hv' : v ∈ e.ker := hk ▸ hv
    have hv0 : e v = 0 := hv'
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩
  exact ((isAtom_range hci _ (pullForm_injective f hf)).le_iff.1 hle).resolve_left hS.1

end GlobalTheory.CompanionTheory.SocleContra

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_of_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  first | exact @GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | exact GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra | (intros; apply GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTopStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twisted_kernel_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N → twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltration
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.KmPow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_quotient_unif_pow (m : ℕ) : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) := by
  have hmax : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {Zls.unif k} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 Zls.irreducible_unif
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k}) := by
    rw [← hmax]
    exact (inferInstance : Finite 𝓀[k])
  have := Ideal.finite_quotient_pow (I := Ideal.span {Zls.unif k}) ⟨{Zls.unif k}, by simp⟩ m
  rwa [Ideal.span_singleton_pow] at this

theorem Km_anti (N : ℕ) {m m' : ℕ} (h : m ≤ m') : Zls.Km k N m' ≤ Zls.Km k N m := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have key : Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g =
      Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)
        (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g) := by
    ext i j
    simp
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [key, hg, map_one]

theorem exists_pow_mem_Km (N m' : ℕ) {m : ℕ} {x : GL (Fin N) k} (hx : x ∈ Zls.Km k N m) :
    ∃ M : ℕ, 0 < M ∧ x ^ M ∈ Zls.Km k N m' := by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  haveI := finite_quotient_unif_pow (k := k) m'
  set f := Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'}))
    with hf
  refine ⟨orderOf (f g), orderOf_pos _, ?_⟩
  rw [← map_pow]
  refine Subgroup.mem_map.2 ⟨g ^ orderOf (f g), ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

theorem KM_antitone_and_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n),
    Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧
    ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd,
      ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  intro k _ _ _ _ n hd
  refine ⟨fun m m' h u hu => Km_anti n (Nat.succ_le_succ h) hu, fun m m' _ u hu => ?_⟩
  obtain ⟨M, hM, hp⟩ := exists_pow_mem_Km n (m' + 1) (show _ ∈ Zls.Km k n (m + 1) from hu)
  refine ⟨M, hM, ?_⟩
  show _ ∈ Zls.Km k n (m' + 1)
  rwa [map_pow]

end GlobalTheory.CompanionTheory.KmPow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernelStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_zero_whittaker_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | exact GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | (intros; apply GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetVolumeFormula
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_of_mem_ker {N m : ℕ} {A : GL (Fin N) 𝒪[k]}
    (hA : A ∈ (Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))).ker) (i j : Fin N) :
    (A : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈
      Ideal.span {Zls.unif k ^ m} := by
  rw [MonoidHom.mem_ker] at hA
  have h := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => u.val i j) hA
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h
  rw [← Ideal.Quotient.eq]
  rw [h]
  by_cases e : i = j
  · subst e
    simp
  · simp [Matrix.one_apply_ne e]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (B : Matrix (Fin N) (Fin N) 𝒪[k])
    (hB : ∀ i j, B i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ Ideal.span {Zls.unif k ^ m}) :
    ∃ b ∈ Zls.Km k N m, (b : Matrix (Fin N) (Fin N) k) = B.map (algebraMap 𝒪[k] k) := by
  set J : Ideal 𝒪[k] := Ideal.span {Zls.unif k ^ m} with hJ
  have hmap : B.map (Ideal.Quotient.mk J) = 1 := by
    ext i j
    have := Ideal.Quotient.eq.2 (hB i j)
    simp only [Matrix.map_apply]
    rw [this]
    by_cases e : i = j
    · subst e
      simp
    · simp [Matrix.one_apply_ne e]
  have hdet : Ideal.Quotient.mk J B.det = 1 := by
    have := RingHom.map_det (Ideal.Quotient.mk J) B
    rw [this]
    show (B.map (Ideal.Quotient.mk J)).det = 1
    rw [hmap, Matrix.det_one]
  have hmem : B.det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, hdet, map_one]
  have hJm : J ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [hJ, Ideal.span_singleton_le_iff_mem]
    have : Zls.unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [Zls.irreducible_unif.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_mem_of_mem _ this m (by omega)
  have hunit : IsUnit B.det := by
    by_contra hn
    have h1 : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 := hJm hmem
    have h3 : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h3
  let G : GL (Fin N) 𝒪[k] := Matrix.GeneralLinearGroup.mk'' B hunit
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) G, ?_, ?_⟩
  · refine ⟨G, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    have h := congrFun (congrFun hmap i) j
    simpa [G, Matrix.GeneralLinearGroup.map_apply] using h
  · rfl

theorem conj_mem_Km {N m : ℕ} {p b : GL (Fin N) k} (hp : p ∈ KO k (Fin N)) (hb : b ∈ Zls.Km k N m) :
    p * b * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨A, hA, rfl⟩ := hb
  refine ⟨P * A * P⁻¹, ?_, by simp⟩
  exact (MonoidHom.normal_ker _).conj_mem A hA P

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    ((Zls.diagPow k N lam : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ lam i) := by
  ext i j
  simp [Zls.diagPow, Zls.unifU, Matrix.diagonal_apply]

theorem exists_cover (N m : ℕ) (hm : 1 ≤ m) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ s : Finset (GL (Fin N) k),
      s.card ≤ Nat.card 𝓀[k] ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, ∃ c ∈ s, ∃ b ∈ Zls.Km k N m,
        x * Zls.diagPow k N lam * y = c * b := by
  classical
  obtain ⟨s0, hcard, hs0⟩ := GlobalTheory.CompanionTheory.KmCover.double_coset_cover 𝒪[k] k N (Zls.unif k) m
    Zls.irreducible_unif hm lam hlam
  let f : Matrix (Fin N) (Fin N) k → GL (Fin N) k := fun M =>
    if h : ∃ c : GL (Fin N) k, c.val = M then h.choose else 1
  refine ⟨s0.image f, Finset.card_image_le.trans hcard, ?_⟩
  rintro x ⟨A1, hA1, rfl⟩ y ⟨A2, hA2, rfl⟩
  obtain ⟨M, hM, B, hB, e⟩ := hs0 A1.val A2.val (entries_of_mem_ker hA1) (entries_of_mem_ker hA2)
  obtain ⟨b, hb, hbv⟩ := exists_mem_Km hm B hB
  set X : GL (Fin N) k := Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A1 *
    Zls.diagPow k N lam * Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A2 with hX
  have hXv : X.val = M * b.val := by
    rw [hbv, ← e, hX, Units.val_mul, Units.val_mul, diagPow_val]
    rfl
  have hex : ∃ c : GL (Fin N) k, c.val = M := by
    refine ⟨X * b⁻¹, ?_⟩
    rw [Units.val_mul, hXv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨f M, Finset.mem_image_of_mem f hM, b, hb, ?_⟩
  apply Units.ext
  have hf : (f M).val = M := by
    simp only [f, dif_pos hex]
    exact hex.choose_spec
  rw [Units.val_mul (f M) b, hf]
  exact hXv

theorem measure_translated_doubleCoset_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  intro k _ _ _ _ N _ _ μ hμ m hm p1 p2 hp1 hp2 g
  classical
  obtain ⟨hanti, hgap⟩ := GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N g
  obtain ⟨s, hcard, hcov⟩ := exists_cover (k := k) N m hm (Zls.lamOf g) hanti
  rw [hgap] at hcard
  set U : Set (AdGL k N) :=
    (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k)) with hU
  let T : GL (Fin N) k → Set (AdGL k N) := fun c =>
    (fun q => (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * q) ⁻¹' U
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m,
      ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2} ⊆ ⋃ c ∈ s, T c := by
    rintro _ ⟨h, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc, b, hb, e⟩ := hcov x hx y hy
    refine Set.mem_biUnion hc ?_
    refine ⟨p2⁻¹ * b * p2, ?_, ?_⟩
    · have := conj_mem_Km (inv_mem hp2) hb
      simpa using this
    · have e2 : p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2 = p1 * (c * b) * p2 := by
        rw [← e]
        group
      rw [e2]
      show (QuotientGroup.mk (p2⁻¹ * b * p2) : AdGL k N) =
        (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * QuotientGroup.mk (p1 * (c * b) * p2)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      group
  calc μ _ ≤ μ (⋃ c ∈ s, T c) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ (T c) := measure_biUnion_finset_le _ _
    _ = ∑ _c ∈ s, μ U := Finset.sum_congr rfl fun c _ => measure_preimage_mul μ _ U
    _ = (s.card : ENNReal) * μ U := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard

end GlobalTheory.CompanionTheory.KmVolume
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k), x.IsCusp → (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | exact GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp | (intros; apply GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_involutive : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k), dualCl (dualCl x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | exact GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl | (intros; apply GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivariantFunctionalsEqDualAnnihilator
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.TwistedDual

theorem rank_le_one_iff_rank_dual_le_one (W : Type) [AddCommGroup W] [Module ℂ W] :
    Module.rank ℂ W ≤ 1 ↔ Module.rank ℂ (Module.Dual ℂ W) ≤ 1 := by
  by_cases hW : Module.Finite ℂ W
  · have h : Module.rank ℂ (Module.Dual ℂ W) = Module.rank ℂ W := by
      rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, Subspace.dual_finrank_eq]
    rw [h]
  · have hinf : Cardinal.aleph0 ≤ Module.rank ℂ W := by
      by_contra hlt
      exact hW (Module.rank_lt_aleph0_iff.1 (not_le.1 hlt))
    have hone : (1 : Cardinal) < Module.rank ℂ W :=
      lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf
    have hdual : Module.rank ℂ W < Module.rank ℂ (Module.Dual ℂ W) := by
      simpa using lift_rank_lt_rank_dual (K := ℂ) (V := W) hinf
    exact iff_of_false (not_le.2 hone) (not_le.2 (hone.trans hdual))

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem equivariantFunctionals_eq_dualAnnihilator (ρ : Representation ℂ G V) (N : Subgroup G)
    (θ : N →* ℂˣ) :
    GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ)) =
      (twKer ρ N θ).dualAnnihilator := by
  ext ℓ
  rw [GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    have hle : twKer ρ N θ ≤ LinearMap.ker ℓ := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      simp [h n v]
    exact hle hw
  · intro h n v
    have hmem : ρ (n : G) v - ((θ n : ℂˣ) : ℂ) • v ∈ twKer ρ N θ :=
      Submodule.subset_span ⟨n, v, rfl⟩
    have h0 := h _ hmem
    simp only [map_sub, map_smul, smul_eq_mul] at h0
    exact sub_eq_zero.1 h0

theorem rank_twJacquet_le_one_iff (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ
        (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1 := by
  rw [equivariantFunctionals_eq_dualAnnihilator,
    ← (twKer ρ N θ).dualQuotEquivDualAnnihilator.rank_eq]
  exact rank_le_one_iff_rank_dual_le_one _

end GlobalTheory.CompanionTheory.TwistedDual

end
end

