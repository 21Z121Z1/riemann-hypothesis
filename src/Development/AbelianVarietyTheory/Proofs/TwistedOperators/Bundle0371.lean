import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroDiscreteSeriesInfiniteHom
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finset_sum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ c.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · rw [← hFx']; exact hF
  · rw [← hFx']; exact hPF

end GlobalTheory.EvenOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLatticeStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  first | exact @GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | exact GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | (intros; apply GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCentralizerMeasuresFromUnitaryTorus
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllMeas

open GlobalTheory.RestrMeas

theorem isHaarProd_map_all {X X' W V : Type} {Ya Ya' : W → Type} {Yf Yf' : V → Type} [Fintype W]
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [MeasurableSpace X'] [BorelSpace X']
    [∀ w, Group (Ya w)] [∀ w, TopologicalSpace (Ya w)] [∀ w, IsTopologicalGroup (Ya w)]
    [∀ w, MeasurableSpace (Ya w)] [∀ w, BorelSpace (Ya w)]
    [∀ w, Group (Ya' w)] [∀ w, TopologicalSpace (Ya' w)] [∀ w, IsTopologicalGroup (Ya' w)]
    [∀ w, MeasurableSpace (Ya' w)] [∀ w, BorelSpace (Ya' w)]
    [∀ v, Group (Yf v)] [∀ v, TopologicalSpace (Yf v)] [∀ v, IsTopologicalGroup (Yf v)]
    [∀ v, MeasurableSpace (Yf v)] [∀ v, BorelSpace (Yf v)]
    [∀ v, Group (Yf' v)] [∀ v, TopologicalSpace (Yf' v)] [∀ v, IsTopologicalGroup (Yf' v)]
    [∀ v, MeasurableSpace (Yf' v)] [∀ v, BorelSpace (Yf' v)]
    {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)}
    {pa' : ∀ w, X' →* Ya' w} {pf' : ∀ v, X' →* Yf' v} {K' : ∀ v, Subgroup (Yf' v)}
    {μa : ∀ w, Measure (Ya' w)} {μf : ∀ v, Measure (Yf' v)} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K' μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w, Ya' w ≃ₜ* Ya w) (ef : ∀ v, Yf' v ≃ₜ* Yf v)
    (ha : ∀ w x, pa w (e x) = ea w (pa' w x)) (hf : ∀ v x, pf v (e x) = ef v (pf' v x))
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hKK : ∀ᶠ v in cofinite, ∀ t, ef v t ∈ K v ↔ t ∈ K' v) :
    IsHaarProd pa pf K (fun w => (μa w).map (ea w)) (fun v => (μf v).map (ef v)) (ν.map e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ma : ∀ w s, (μa w).map (ea w) s = μa w (ea w ⁻¹' s) := fun w s =>
    (ea w).toHomeomorph.toMeasurableEquiv.map_apply s
  have mf : ∀ v s, (μf v).map (ef v) s = μf v (ef v ⁻¹' s) := fun v s =>
    (ef v).toHomeomorph.toMeasurableEquiv.map_apply s
  have m : ∀ s, ν.map e s = ν (e ⁻¹' s) := fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and hKK)
  refine ⟨fun w => (ea w).isHaarMeasure_map _, fun v => (ef v).isHaarMeasure_map _, e.isHaarMeasure_map _,
    isCylProd_of_large (K := fun v => (K v : Set (Yf v))) (fun v => (hK v).measurableSet) S₀ (fun v hv => ?_)
      (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  · rw [mf, ← (hS v hv).1]
    exact congrArg _ (Set.ext (hS v hv).2)
  · simp only [ma, mf, m]
    rw [← h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) _ _
      (fun w => (map_continuous (ea w)).measurable (hA w)) fun v hv => (map_continuous (ef v)).measurable (hB v hv)]
    refine congrArg ν (Set.ext fun x => ?_)
    simp only [mem_preimage, mem_cyl, ha, hf]
    exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
      (hS v fun h' => hv (hs h')).2 _

theorem isFundamentalDomain_map {T C : Type} [Group T] [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    [Group C] [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] (e : T ≃ₜ* C) {Γ : Subgroup T}
    {Γ' : Subgroup C} (h : ∀ t, e t ∈ Γ' ↔ t ∈ Γ) {μ : Measure T} {D : Set T} (hD : IsFundamentalDomain Γ D μ) :
    IsFundamentalDomain Γ' (e '' D) (μ.map e) ∧ μ.map e (e '' D) = μ D := by
  refine ⟨hD.image_of_equiv e.toEquiv ?_ (subEquiv e h).symm.toEquiv fun g x => ?_, ?_⟩
  · exact (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ⟨(map_continuous e).measurable, rfl⟩).quasiMeasurePreserving
  · change e (e.symm g * x) = g * e x
    rw [map_mul, e.apply_symm_apply]
  · rw [show μ.map e (e '' D) = μ (e ⁻¹' (e '' D)) from e.toHomeomorph.toMeasurableEquiv.map_apply _,
      e.injective.preimage_image]

theorem hasOrbInt_comap_congr {H : Type} [Group H] [MeasurableSpace H] {γ γ' : H} (h : γ = γ') (m μ : Measure H)
    (f : H → ℂ) (c : ℂ) : HasOrbInt μ γ (m.comap Subtype.val) f c ↔ HasOrbInt μ γ' (m.comap Subtype.val) f c := by
  subst h
  rfl

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem mapH_diagH {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k k' : Type} [CommRing k] [Algebra F k] [CommRing k']
    [Algebra F k'] (ψ : k →ₐ[F] k') (g : GRat σ J) : mapH σ J ψ (diagH σ J k g) = diagH σ J k' g := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] g.1.1 i j) = (1 : k') ⊗ₜ[F] g.1.1 i j
  simp

theorem diagH_surjective {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Function.Surjective (diagH σ J F) := by
  intro g
  let l : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
  have hl : ∀ y, (1 : F) ⊗ₜ[F] l y = y := fun y => (Algebra.TensorProduct.lid F E).symm_apply_apply y
  have hl' : ∀ y, l ((1 : F) ⊗ₜ[F] y) = y := fun y => (Algebra.TensorProduct.lid F E).apply_symm_apply y
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (sigR F σ) (σ : E →+* E) l (fun y => ?_) (JR F J) J
    (Matrix.ext fun i j => hl' _) g, Subtype.ext (Units.ext (Matrix.ext fun i j => hl _))⟩
  conv_rhs => rw [← hl y]
  exact (hl' (σ (l y))).symm

variable [NumberField F] [NumberField E] {σ}

theorem exists_equiv (hσ : IsCMExt F E σ) {r : ℕ} {P : PPol σ r} {J : Matrix (Fin r) (Fin r) E} (hJ : IsHermND σ J)
    {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {x : plusUnits P k} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)} (h : IsIsom P k J x.1.1 φ)
    {γ : HA k σ J} (hγ : gam h = γ) :
    ∃ e : Tor P k ≃ₜ* cent γ, (∀ t, (e t).1 = torEmb h t) ∧ ∀ (dt : Measure (Tor P k)) (x' : plusUnits P k)
      (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), gam h' = γ →
      ∀ μ f c, HasOrbInt μ (gam h') (centMeas h' dt) f c ↔ HasOrbInt μ γ (dt.map e) f c := by
  subst hγ
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r r P J hJ k x φ h
  refine ⟨e, he, fun dt x' φ' h' hγ μ f c => ?_⟩
  have h1 : torEmb h' = torEmb h := MonoidHom.ext fun t => by
    simpa using (GlobalTheory.TrEll.cls_conj_torus F E σ hσ r r P J hJ k x φ h x' φ' h').2.2.1 1 (by simpa using hγ) t
  rw [← hm, centMeas, centMeas, h1]
  exact hasOrbInt_comap_congr hγ _ _ _ _

theorem exists_isCentProd_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  intro F E _ _ _ _ _ σ hσ r P J hJ L _ γ hP dta dtf dt hdt
  obtain ⟨P', hP', _, x₀, φ₀, h₀, -, hγ₀⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hσ r J hJ).2 γ (hP ▸ P.2.2.1)
  obtain rfl : P = P' := Subtype.ext (hP.symm.trans hP')
  obtain ⟨xA, φA, hA, -, hγA, htA⟩ := GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ F (AF F) (Algebra.ofId F (AF F)) x₀ φ₀ h₀
  rw [hγ₀, mapH_diagH] at hγA
  replace hγA : gam hA = ratEmb σ J γ := hγA
  choose xf φf hf _ hγf htf using fun v : HeightOneSpectrum (𝓞 F) =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) (Fv F v) (evFin F v) xA φA hA
  choose xa φa ha _ hγa hta using fun w : InfinitePlace F =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) w.Completion (evInf F w) xA φA hA
  rw [hγA] at hγf hγa
  replace hγf : ∀ v, gam (hf v) = proj σ J v (ratEmb σ J γ) := hγf
  replace hγa : ∀ w, gam (ha w) = projArch σ J w (ratEmb σ J γ) := hγa
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  obtain ⟨e, he, -⟩ := exists_equiv hσ hJ hA hγA
  choose ef hef hof using fun v => exists_equiv hσ hJ (hf v) (hγf v)
  choose ea hea hoa using fun w => exists_equiv hσ hJ (ha w) (hγa w)
  refine ⟨fun w => (dta w).map (ea w), fun v => (dtf v).map (ef v), dt.map e, ?_, ?_,
    fun v x φ h hγ => hof v _ x φ h hγ, fun w x φ h hγ => hoa w _ x φ h hγ⟩
  · refine isHaarProd_map_all hdt e ea ef (fun w t => Subtype.ext ?_) (fun v t => Subtype.ext ?_)
      (restrGroup_cent L _).isOpen_K ?_
    · rw [hea]
      exact (congrArg (projArch σ J w) (he t)).trans (hta w t).symm
    · rw [hef]
      exact (congrArg (proj σ J v) (he t)).trans (htf v t).symm
    · filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hσ r P J hJ L, eventually_proj_mem_stabLoc σ J L (ratEmb σ J γ)]
        with v h1 h2 t
      rw [Subgroup.mem_subgroupOf, hef]
      exact h1.2.2.1 _ _ (hf v) (hγf v ▸ h2) t
  · have := hdt.2.2.1
    have hΓ : ∀ t, e t ∈ (ratPts σ J).subgroupOf (cent (ratEmb σ J γ)) ↔ t ∈ ratPts (star' P) (one₁ P) := by
      intro t
      rw [Subgroup.mem_subgroupOf, ← range_ratEmb, ← range_ratEmb]
      constructor
      · rintro ⟨δ, hδ⟩
        have h1 : δ * γ = γ * δ := ratEmb_injective σ J (by
          rw [map_mul, map_mul, hδ]; exact mem_cent.1 (e t).2)
        letI : TopologicalSpace F := ⊥
        haveI : DiscreteTopology F := ⟨rfl⟩
        obtain ⟨e₀, he₀, -⟩ := exists_equiv hσ hJ h₀ hγ₀
        obtain ⟨s, hs⟩ := e₀.surjective ⟨diagH σ J F δ, mem_cent.2 (by rw [← map_mul, ← map_mul, h1])⟩
        obtain ⟨s, rfl⟩ := diagH_surjective (star' P) (one₁ P) s
        refine ⟨s, e.injective (Subtype.ext ?_)⟩
        have h2 := htA (diagH _ _ F s)
        rw [← he₀, hs, mapH_diagH, mapH_diagH] at h2
        rw [he, ← hδ]
        exact h2
      · rintro ⟨s, rfl⟩
        obtain ⟨δ, hδ⟩ := diagH_surjective σ J (torEmb h₀ (diagH _ _ F s))
        have h2 := htA (diagH _ _ F s)
        rw [← hδ, mapH_diagH, mapH_diagH] at h2
        exact ⟨δ, ((he _).trans h2).symm⟩
    have hD := isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
    obtain ⟨h1, h2⟩ := isFundamentalDomain_map e hΓ hD
    exact ⟨_, h1, h2.trans (quotMeasure_univ hD).symm⟩

end GlobalTheory.TrEllMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonLevelGrowthExponentGKMapStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_growth_exponent_gKMap : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ → ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧ ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  first | exact @GlobalTheory.GKUnif.exists_level_exponent | exact GlobalTheory.GKUnif.exists_level_exponent | (intros; apply GlobalTheory.GKUnif.exists_level_exponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinAvgSpan

open Formalism.REAL MeasureTheory GlobalTheory.SeriesToClosure Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom

theorem continuous_integral_K {n : ℕ} {ε : Fin n → Bool} {X : Type*} [TopologicalSpace X] (F : X → KG ε → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ k, F x k ∂(muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ k, g k ∂(muK ε)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (GlobalTheory.ExpansionAverage.integrable_K g.continuous)
          (GlobalTheory.ExpansionAverage.integrable_K h.continuous)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hL : Continuous L := AddMonoidHomClass.continuous_of_bound L ((muK ε).real Set.univ) fun g => by
    show ‖∫ k, g k ∂(muK ε)‖ ≤ _
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      ContinuousMap.norm_coe_le_norm g k)).trans (le_of_eq (mul_comm _ _))
  exact hL.comp (ContinuousMap.curry ⟨_, hF⟩).continuous

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_conjAt (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) :
    Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
    fun k => conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))

theorem continuous_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    Continuous (Function.uncurry fun (x : GA D V) (k : KG ε) => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) :=
  (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul ((continuous_conjAt hθ hP hJ).comp continuous_snd)))

theorem integrable_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) (x : GA D V) :
    Integrable (fun k => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) (muK ε) :=
  GlobalTheory.ExpansionAverage.integrable_K (he.mul (hφ.comp (continuous_const.mul (continuous_conjAt hθ hP hJ))))

theorem continuous_avg (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) : Continuous (avg θ V τ ε P e φ) :=
  continuous_integral_K _ (continuous_integrand hθ hP hJ he hφ)

theorem avg_add_left (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e₁ e₂ : KG ε → ℂ} (h₁ : Continuous e₁) (h₂ : Continuous e₂) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    avg θ V τ ε P (e₁ + e₂) φ = avg θ V τ ε P e₁ φ + avg θ V τ ε P e₂ φ := funext fun x => by
  simp only [avg, Pi.add_apply, add_mul]
  exact integral_add (integrable_integrand hθ hP hJ h₁ hφ x) (integrable_integrand hθ hP hJ h₂ hφ x)

theorem avg_smul_left (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P (c • e) φ = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem avg_add_right (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ₁ φ₂ : GA D V → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    avg θ V τ ε P e (φ₁ + φ₂) = avg θ V τ ε P e φ₁ + avg θ V τ ε P e φ₂ := funext fun x => by
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hθ hP hJ he h₁ x) (integrable_integrand hθ hP hJ he h₂ x)

theorem avg_smul_right (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P e (c • φ) = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_left_comm (e _) c]
  exact integral_const_mul c _

theorem rTr_avg_same (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : P * g * P⁻¹ ∈ Kset ε) :
    ∃ k₀ : KG ε, ∀ (e : KG ε → ℂ) (φ : GA D V → ℂ),
      rTr V (atTau θ V τ g) (avg θ V τ ε P e φ) = avg θ V τ ε P (fun k => e (k₀⁻¹ * k)) φ := by
  obtain ⟨k₀, hk₀'⟩ : P * g * P⁻¹ ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
  have hk₀ : toMK k₀ = P * g * P⁻¹ := hk₀'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have eg : g = P⁻¹ * toMK k₀ * P := by
    rw [hk₀]
    calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul _ hd, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨k₀, fun e φ => funext fun x => ?_⟩
  have key : ∀ k : KG ε, atTau θ V τ g * atTau θ V τ (P⁻¹ * toMK k * P) =
      atTau θ V τ (P⁻¹ * toMK (k₀ * k) * P) := fun k => by
    rw [eg, ← at_mul hθ hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k₀)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))]
    rfl
  simp only [rTr, avg, mul_assoc x, key]
  rw [← integral_mul_left_eq_self (μ := muK ε)
    (fun k => e (k₀⁻¹ * k) * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) k₀]
  simp only [inv_mul_cancel_left]

theorem rTr_avg_other (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    rTr V (atTau θ V τ' g) (avg θ V τ ε P e φ) = avg θ V τ ε P e (rTr V (atTau θ V τ' g) φ) := funext fun x => by
  simp only [rTr, avg, mul_assoc x]
  congr 1
  funext k
  rw [GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _
    (conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))) g hg]

end GlobalTheory.KFinAvgSpan

namespace GlobalTheory.KFinAvgSpan

set_option maxHeartbeats 1600000 in

theorem exists_stab_insert : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  intro D θ hθ N τ e he s hτs W' hW'fin hW'c hW'stab
  obtain ⟨F, hFfin, heF, hFc, hFtr⟩ := he
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI := hFfin
  haveI := hW'fin
  let B : F →ₗ[ℂ] W' →ₗ[ℂ] (GA D N.V → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ)
        (b : GA D N.V → ℂ))
      (fun a₁ a₂ b => avg_add_left hθ hP hJ (hFc _ a₁.2) (hFc _ a₂.2) (hW'c _ b.2))
      (fun c a b => avg_smul_left c _ _)
      (fun a b₁ b₂ => avg_add_right hθ hP hJ (hFc _ a.2) (hW'c _ b₁.2) (hW'c _ b₂.2))
      (fun c a b => avg_smul_right c _ _)
  have hB : ∀ (a : F) (b : W'), TensorProduct.lift B (a ⊗ₜ b) =
      GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ) :=
    fun a b => by rw [TensorProduct.lift.tmul]; rfl
  have hcont : ∀ t, Continuous (TensorProduct.lift B t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact continuous_const
    | tmul a b => rw [hB]; exact continuous_avg hθ hP hJ (hFc _ a.2) (hW'c _ b.2)
    | add u v hu hv => rw [map_add]; exact hu.add hv
  refine ⟨LinearMap.range (TensorProduct.lift B), inferInstance, ?_, ?_, fun f hf => ⟨⟨e, heF⟩ ⊗ₜ ⟨f, hf⟩, hB _ _⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact hcont t
  · intro τ'' hτ'' g hg hK w hw
    obtain ⟨t, rfl⟩ := hw
    suffices h : ∀ (a : F) (b : W'), rTr N.V (atTau θ N.V τ'' g)
        (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)) ∈
          LinearMap.range (TensorProduct.lift B) by
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | tmul a b => rw [hB]; exact h a b
      | add u v hu hv =>
        rw [map_add]
        exact add_mem hu hv
    intro a b
    rcases hτ'' with h | hs
    · rw [h] at hK ⊢
      obtain ⟨k₀, hk⟩ := rTr_avg_same hθ hP hJ hK
      have hk' := hk (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)
      refine ⟨⟨_, (hFtr _ a.2 k₀⁻¹).1⟩ ⊗ₜ b, ?_⟩
      rw [hB, hk']
    · have hne : τ ≠ τ'' := fun h => hτs (h ▸ hs)
      rw [rTr_avg_other hθ hP hJ hne hg]
      exact ⟨a ⊗ₜ ⟨_, hW'stab τ'' hs g hg hK b b.2⟩, hB _ _⟩

end GlobalTheory.KFinAvgSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  first | exact @GlobalTheory.HoweGlobal.TensorMap.exists_tensL | exact GlobalTheory.HoweGlobal.TensorMap.exists_tensL | (intros; apply GlobalTheory.HoweGlobal.TensorMap.exists_tensL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroDiscreteSeriesInfiniteHomStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_discreteSeriesInfiniteHom : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∃ Φ ∈ homDS M π ⊤, Φ ≠ 0 := by
  first | exact @GlobalTheory.TensorHom.exists_ne_zero_homDS | exact GlobalTheory.TensorHom.exists_ne_zero_homDS | (intros; apply GlobalTheory.TensorHom.exists_ne_zero_homDS <;> assumption)
end

