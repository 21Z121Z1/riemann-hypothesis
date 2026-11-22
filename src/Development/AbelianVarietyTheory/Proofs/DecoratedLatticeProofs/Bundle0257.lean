import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalDoubleCosetRepresentativeBounds
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.RepsOnto
open GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL

theorem val_unif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem denseRange_toLoc {E k : Type} [Field E] [Field k] [TopologicalSpace k] {ι : E →+* k} (hι : DenseRange ι)
    {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) : DenseRange (toLoc ι e e') := by
  have h1 : DenseRange (Pi.map fun (_ : A) => Pi.map fun (_ : B) => (ι : E → k)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hι
  refine Dense.mono ?_ h1
  rintro _ ⟨M, rfl⟩
  refine ⟨Matrix.toLin' ((Matrix.of M).submatrix e.symm e'.symm), ?_⟩
  rw [toLoc_eq, LinearMap.toMatrix'_toLin']
  ext i l
  simp

open GlobalTheory.LatClass GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice in

theorem exists_bounded_rep : ∀ (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ j c (h : j + 1 + c = s) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1 + 1)) k),
    (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1 + 1) 1,
      GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) →
    ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
    flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 →
    ∃ g₁ : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g₁ =
        DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h' ∧
      ∀ κ ∈ ((W.T s R).lev (j + 1) (c + 1) (by omega)).J,
        latOf 1 ≤ latOf (g₁ * κ) ∧ ∀ y ∈ latOf (g₁ * κ), ((W.ϖ : k) ^ (j + 1)) • y ∈ latOf 1 := by
  intro R k _ _ _ _ s W _ _ ν hν j c h g hr h' hf
  haveI := hν.1
  have hϖ := val_unif W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  have H : (∀ j c h x, (W.T s R).Phi j c h x ≠ 0 → IntM x) ∧
      (∀ j c h x y, MaxM y → (W.T s R).Phi j c h (x + y) = (W.T s R).Phi j c h x) ∧
      ∀ j c h, ((W.T s R).lev j c h).J ≤ KO k _ :=
    GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s _ _ _ _ W.δ W.tame W.η _ _ (fun _ _ _ => rfl)
  obtain ⟨hs, hp, hJ⟩ := H
  obtain ⟨r, hr, e', z', he', hz', hl⟩ := hr
  rw [lat_bas hb, ← nfBasis_one] at hl
  obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c W.ψ ν _ _ g h' hf r hr)
  obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ W.cond he' hz'
    (hl ▸ om_supp (hs _ _ _) (r * g) h') (hl ▸ om_per hϖ (hp _ _ _) (r * g) h') h0
  refine ⟨r₂ * h', ((DoubleCoset.eq _ _ _ _).2 ⟨r₂, hr₂, 1, one_mem _, (mul_one _).symm⟩).symm, fun κ hκ => ?_⟩
  rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ _ _ _ hκ)), mul_one, hl₂]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [mem_latOf_one] at hy
    exact mem_normal.2 ⟨fun r => sub_mem (hy _) (mul_mem (hy _) (hz r)),
      fun i => pow_mono hϖ (he i).2 (mem_pow_zero.2 (hy _))⟩
  · obtain ⟨h1, h2⟩ := mem_normal.1 hy
    have h3 : ∀ i, (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) * y (.inr i) ∈ 𝒪[k] := fun i =>
      mem_pow_zero.1 (zpow_mul_mem_pow.2 (pow_mono hϖ (by have := he i; omega) (h2 i)))
    have h4 : (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) ∈ 𝒪[k] := mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by omega))
    rw [mem_latOf_one, ← zpow_natCast]
    rintro (r | i)
    · convert add_mem (mul_mem h4 (h1 r)) (mul_mem (h3 0) (hz r)) using 1
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    · exact h3 i

theorem exists_toLocGL_mem : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A : Type) [Fintype A] [DecidableEq A] (a : ℕ) (e : A ≃ Fin a) (U : Set (GL A k)),
    IsOpen U → U.Nonempty → ∃ γ : (Fin a → E) ≃ₗ[E] (Fin a → E), toLocGL ι e γ ∈ U := by
  intro E k _ _ _ _ _ ι hι A _ _ a e U hU ⟨g₀, hg₀⟩
  haveI : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hS : IsOpen {M : Matrix A A k | M.det ≠ 0} := isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let F : {M : Matrix A A k | M.det ≠ 0} → GL A k := fun M => GeneralLinearGroup.mkOfDetNeZero M.1 M.2
  have hF : Continuous F := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have : (fun M => ((F M)⁻¹ : GL A k).val) = fun M => (M.1.det)⁻¹ • M.1.adjugate := by
      funext M
      rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
      rfl
    rw [this]
    exact ((continuous_subtype_val.matrix_det).inv₀ fun M => M.2).smul continuous_subtype_val.matrix_adjugate
  have hV := hS.isOpenMap_subtype_val _ (hU.preimage hF)
  have hne : (Subtype.val '' (F ⁻¹' U)).Nonempty := by
    refine ⟨_, ⟨g₀.val, g₀.det_ne_zero⟩, ?_, rfl⟩
    have : F ⟨g₀.val, g₀.det_ne_zero⟩ = g₀ := Units.ext rfl
    rw [Set.mem_preimage, this]
    exact hg₀
  obtain ⟨x, M, hM, hx⟩ := (denseRange_toLoc hι e e).exists_mem_open hV hne
  have hd : LinearMap.det x ≠ 0 := by
    intro h0
    have h1 := M.2
    rw [Set.mem_setOf_eq, hx, toLoc_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self,
      LinearMap.det_toMatrix', h0, map_zero] at h1
    exact h1 rfl
  have hbij : Function.Bijective x := (Module.End.isUnit_iff x).1 ((LinearMap.isUnit_iff_isUnit_det x).2 hd.isUnit)
  refine ⟨LinearEquiv.ofBijective x hbij, ?_⟩
  have : toLocGL ι e (LinearEquiv.ofBijective x hbij) = F M := Units.ext hx.symm
  rw [this]
  exact hM

theorem exists_toLoc_ne_zero : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A B : Type) [Fintype A] [Fintype B] (a b : ℕ) (e : A ≃ Fin a) (e' : B ≃ Fin b)
    (f : Matrix A B k → ℂ), IsLocallyConstant f → f ≠ 0 → ∃ x : (Fin b → E) →ₗ[E] (Fin a → E), f (toLoc ι e e' x) ≠ 0 := by
  intro E k _ _ _ _ _ ι hι A B _ _ a b e e' f hf hne
  exact (denseRange_toLoc hι e e').exists_mem_open (hf {z | z ≠ 0}) (Function.ne_iff.1 hne)

theorem toLoc_mulVec {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a)
    (x : (Fin a → E) →ₗ[E] (Fin a → E)) (y : Fin a → E) :
    (toLoc ι e e x *ᵥ fun i => ι (y (e i))) = fun i => ι (x y (e i)) := by
  funext i
  rw [toLoc_eq, ← LinearMap.toMatrix'_mulVec]
  simp only [mulVec, dotProduct, map_sum, map_mul, map_apply, submatrix_apply]
  exact Equiv.sum_comp e fun l => ι (LinearMap.toMatrix' x (e i) l) * ι (y l)

theorem bounds_of_isGL : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (P : HeightOneSpectrum (𝓞 X.E)) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ),
    IsCompl P (qOf P) ι ϖ → P ∉ Pr.vGs → ∀ (j c n : ℕ) (γ : AutY X R j) (g' : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι γ g' → latOf 1 ≤ latOf g' → (∀ y ∈ latOf g', ((ϖ : k) ^ n) • y ∈ latOf 1) →
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ n) • γ x ∈ lamYat (Pr := Pr) (R := R) j P := by
  intro X Pr R P k _ _ _ _ ι ϖ hC hP j c n γ g' ⟨e, _, hg⟩ h1 h2 x hx
  have hmem : ∀ y, y ∈ lamYat (Pr := Pr) (R := R) j P ↔ (fun i => ι (y (e i))) ∈ latOf (1 : GL _ k) := fun y => by
    unfold lamYat LocE.lamY LocE.sclLat stdAt
    rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice, mem_latOf_one]
    simp only [hC.int]
    rw [e.surjective.forall]
    simp [LocE.scE]
  obtain rfl : g' = toLocGL ι e γ := Units.ext hg
  rw [hmem] at hx
  refine ⟨(hmem _).2 (mem_latOf_one.2 ?_), (hmem _).2 ?_⟩
  · have h3 : ∀ i, (toLoc ι e e γ.symm.toLinearMap *ᵥ fun i => ι (x (e i))) i ∈ 𝒪[k] := h1 hx
    rw [toLoc_mulVec] at h3
    exact h3
  · have h3 : (toLocGL ι e γ).val *ᵥ (fun i => ι (x (e i))) ∈ latOf (toLocGL ι e γ * 1) := (mulVec_mem_latOf _).2 hx
    rw [mul_one] at h3
    have h4 := h2 _ h3
    change (ϖ : k) ^ n • (toLoc ι e e γ.toLinearMap *ᵥ fun i => ι (x (e i))) ∈ _ at h4
    rw [toLoc_mulVec, hC.unif] at h4
    convert h4 using 1
    funext i
    simp

theorem ordX_exists (R : Ranks) (j : ℕ) : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), IsOrd xPos e := by
  have hN : R.k + j + j * R.t + 0 = R.N j := by simp only [Ranks.N]; ring
  refine ⟨(Equiv.sumEmpty _ (Fin 0)).symm.trans (ordY R.k R.t j 0 _ hN), fun a => ?_⟩
  have := ordY_isOrd R.k R.t j 0 _ hN (Sum.inl a)
  simpa [yPos] using this

end GlobalTheory.TwBridge.RepsOnto

open GlobalTheory.TwBridge.RepsOnto GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL in

theorem GlobalTheory.TwBridge.repsOnto : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g → (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1 + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) → ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 → ∃ γ : AutY X R (j + 1), (∃ g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, IsGL ι γ g' ∧ DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g' = DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h') ∧ (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hI j c h al g hg hr h' hf
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨g₁, hdc, hbd⟩ := exists_bounded_rep R k s W ν hν j c h g hr h' hf
  set J := ((W.T s R).lev (j + 1) (c + 1) (by omega)).J with hJ
  have hreg : (W.T s R).Regular := GlobalTheory.StepData.Chain.ofTwist_regular _ _ _ _ _
  have hlaws : (W.T s R).Laws := GlobalTheory.StepData.Chain.ofTwist_laws _ _ _ W.unr _ _
  have hJo := (hreg.2.2 (j + 1) (c + 1) (by omega)).1
  have hm := hA.steps
  have hN : R.k + (j + 1) + (j + 1) * R.t + (c + 1) = R.N (j + 1) + cOf R (j + 1) := by
    have e2 : R.N (j + 1) = R.k + (j + 1) + (j + 1) * R.t := by simp only [Ranks.N]; ring
    rw [e2]; simp only [cOf]; rw [hm]; omega
  have ho : IsOrdY (ordY R.k R.t (j + 1) (c + 1) _ hN) := by
    have := ordY_isOrd R.k R.t (j + 1) (c + 1) _ hN
    have e2 : R.k + (j + 1) + (j + 1) * R.t = R.N (j + 1) := by simp only [Ranks.N]; ring
    rwa [e2] at this
  obtain ⟨γ, hγ⟩ := exists_toLocGL_mem X.E k ι hA.compl.dense _ _ (ordY R.k R.t (j + 1) (c + 1) _ hN)
    {x | g₁⁻¹ * x ∈ J} (hJo.preimage (continuous_const.mul continuous_id)) ⟨g₁, by simp [J.one_mem]⟩
  set g' := toLocGL ι (ordY R.k R.t (j + 1) (c + 1) _ hN) γ with hg'
  have hgl : IsGL ι γ g' := ⟨_, ho, rfl⟩
  have hκ : g₁⁻¹ * g' ∈ J := hγ
  have hdc' : DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J g' =
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J h' := by
    rw [← hdc]
    exact (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (g₁⁻¹ * g')⁻¹, inv_mem hκ, by group⟩
  obtain ⟨hb1, hb2⟩ := hbd _ hκ
  rw [mul_inv_cancel_left] at hb1 hb2
  have hbd' := bounds_of_isGL X Pr R P.1 k ι W.ϖ hA.compl hA.nmem (j + 1) (c + 1) (j + 1) γ g' hgl hb1 hb2
  refine ⟨γ, ⟨g', hgl, hdc'⟩, hbd', ?_⟩
  have hfl : flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
    have hT := hlaws.1 j (c + 1) (by omega)
    exact (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (by omega) hT rfl hdc'.symm).1 hf
  have hSB := GlobalTheory.RootEx.opE_mem_SB 1 W.ψ ν (GlobalTheory.SplitWeil.om_mem_SB ((W.T s R).mu (j + 1)) g g'
    (hreg.1 j (c + 1) (by omega)))
  obtain ⟨e', he'⟩ := ordX_exists R j
  obtain ⟨e, he⟩ := ordX_exists R (j + 1)
  obtain ⟨x, hx⟩ := exists_toLoc_ne_zero X.E k ι hA.compl.dense _ _ _ _ e e'
    (flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g') hSB.1 hfl
  obtain ⟨A₀, B₀, hAB⟩ := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA j c h (L.h j al P) γ g g' hg hgl
    (hL.boundQ j al P hA.nmem) hbd' (hL.depthQ' P hA.nmem)
  refine ⟨A₀, B₀, fun A' B' h1 h2 hz => hx ?_⟩
  rw [hAB A' B' h1 h2 e' e he' he x]
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSumLat

variable {D : D7}

theorem rat_mulVec_mem_latV {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem dsum_eq' {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA' {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

theorem exists_selfDual_orthAt : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B), IsSelfDualC A LA →
    IsSelfDualC B LB → ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  intro D S A B o LA LB hA hB
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨⟨(hA.1.fg.map _).sup (hB.1.fg.map _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · rw [eq_top_iff]
    intro y _
    have key : ∀ {C : HSp D} (m : Matrix (Fin S.rank) (Fin C.rank) D.host.E) (LC : Lat C), IsSelfDualC C LC →
        (∀ x ∈ LC, m *ᵥ x ∈ LA.map fA ⊔ LB.map fB) → ∀ z, m *ᵥ z ∈ Submodule.span D.host.E
          ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E)) := by
      intro C m LC hC hm z
      have hz : z ∈ Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) := by rw [hC.1.span_eq_top]; trivial
      have : Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) ≤ Submodule.comap (mulVecLin m)
          (Submodule.span D.host.E ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E))) :=
        Submodule.span_le.2 fun x hx => Submodule.subset_span (hm x hx)
      exact this hz
    rw [hsum y]
    exact add_mem (key _ LA hA hiA _) (key _ LB hB hiB _)
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq'] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
    rw [star_add, add_dotProduct, pair_iA', e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq', pair_iA', ← dsum_eq'] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
      rwa [dsum_eq', e2, ← dsum_eq'] at this
  · have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.sum_eq_one, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem_latV _ hiA h.1) (rat_mulVec_mem_latV _ hiB h.2)

end GlobalTheory.OrthSumLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · rw [hC, map_add, map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · rw [hP, hP, map_add, map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      rw [hy1, hC, map_add, map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · rw [hy2, hP, hP, map_add, map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.JacUnimod

theorem jacGrp_rightInv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ ρ d μ hμ
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V₀
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  obtain ⟨hlc, hsc, hbor, hcount⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨ν, 𝓝, hνH, h𝓝, h𝓝1⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  have hnorm := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d
  have hp := GlobalTheory.JacProj.exists_continuous_proj D V V₀ ρ d
  have hc := GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D V V₀ ρ d ν hνH
  let μ₀ : Measure (GA D V₀) := Measure.haar
  have hμ₀ : μ₀.IsHaarMeasure := inferInstance
  haveI := hνH
  haveI : μ₀.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V₀ μ₀ hμ₀
  haveI : ν.IsMulRightInvariant := GlobalTheory.SemiHaar.rightInv_of_fd _ ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed hnorm hp μ₀ ν hμ₀ hνH hc
  obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed hnorm hp
    μ₀ ν hμ₀ hνH hc
  have hH : (semiMeas (flagN d) d.emb0 μ₀ ν).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) d.emb0 hNc d.continuous_embed hnorm μ₀ ν
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) d.emb0 hnorm d.continuous_embed hp
  haveI : LocallyCompactSpace (jacGrp d) := e.symm.isClosedEmbedding.locallyCompactSpace
  let κ : Measure (jacGrp d) := semiMeas (flagN d) d.emb0 μ₀ ν
  haveI hκH : κ.IsHaarMeasure := hH
  haveI hκR : κ.IsMulRightInvariant := hR
  have hk := Measure.isMulLeftInvariant_eq_smul μ κ
  rw [hk]
  infer_instance

end GlobalTheory.JacUnimod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenericTermsPointsAgreeGroupSumsCorankOne
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtMixedModelSourceDualLineLinearFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_mixedModelSource_dualLine_linearForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ Mx D T.rank ρ, Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ x w, HasDerivAt (fun t : ℝ => ψ (symplO S T (d.extX T x) (d.extY T (L t))) * d.mixS T ψ v.μ v.𝓕 f x w) (d.mixS T ψ v.μ v.𝓕 (fun p => deriv (fun t : ℝ => heisO ψ S T (d.extY T (L t)) f p) 0) x w) 0 := by
  first | exact @GlobalTheory.Unf.hasDerivAt_mixS_extY | exact GlobalTheory.Unf.hasDerivAt_mixS_extY | (intros; apply GlobalTheory.Unf.hasDerivAt_mixS_extY <;> assumption)
end

