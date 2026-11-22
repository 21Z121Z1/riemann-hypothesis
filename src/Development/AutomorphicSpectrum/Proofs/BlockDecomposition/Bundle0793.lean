import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0014
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Rs.SatakeVectors PositivityTheory.Rg.Rs.SatakeVectors.SatakeVectorEventually PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinSatPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem satV_of_comp {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : HasSatGL w σ.ρ B) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ h]; exact hψ
  refine ⟨?_, fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hs (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0⟩
  obtain ⟨x, hx⟩ := hs.exists_vec
  obtain ⟨f, h0, hfV, hf⟩ := h
  haveI := σ.irred
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
      (f.intertwiningMap_of_isIntertwiningMap σ.ρ ((finRep E N).comp (locGL E N w)) hf) with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨f x, hfV x, hx.map f hf fun e => hx.1 (hi (by rw [e, map_zero]))⟩

theorem hasSat_of_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : SatV V w B) : HasSatGL w σ.ρ B := by
  obtain ⟨⟨φ, hφ, hφs⟩, -⟩ := hs
  have hfix : ∀ k ∈ KGL w N, finRep E N (locGL E N w k) φ = φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hφs.2.1 k hk
  have hmem : φ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := by
    rw [iSup_range_eq hV w σ h]; exact hφ
  obtain ⟨v, hv0, hv⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (KGL w N : Set _) φ hφs.1 hfix hmem
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w N) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have e : B' = B := ((satV_of_comp hV h hB').2 φ hφ hfix hφs.1).unique hφs
  exact e ▸ hB'

theorem satV_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatV V w B) :
    SatV (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  have L := satLike_map_mulChi hχ (satLike_of_satV h)
  refine ⟨?_, L⟩
  obtain ⟨⟨φ, hφ, hs⟩, -⟩ := h
  have hm : (mulChi m χ) φ ∈ V.map (mulChi m χ).toLinearMap := Submodule.mem_map_of_mem hφ
  refine ⟨_, hm, L _ hm (fun k hk => ?_) fun e => hs.1 ((mulChi m χ).injective (by rw [e, map_zero]))⟩
  rw [finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one, one_smul]
  exact congrArg _ (GlobalTheory.LGrp.mem_fixed.1 hs.2.1 k hk)

def PartSat (w : HeightOneSpectrum (𝓞 E)) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (B : Multiset ℂˣ) : Prop :=
  SatV x.2 w B

variable {n a b : ℕ}

theorem pre_sat_iff (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    D.Sat w B ↔ ∃ l : List (Multiset ℂˣ), List.Forall₂ (PartSat w) (parts D) l ∧ l.sum = B := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨List.ofFn c, ?_, List.sum_ofFn⟩
    refine List.forall₂_iff_get.2 ⟨by simp [parts], fun i h₁ h₂ => ?_⟩
    simp only [parts, List.get_eq_getElem, List.getElem_ofFn]
    exact satV_of_comp (D.discrete _) (D.loc _ w) (hc _).2
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hlen, hg⟩ := List.forall₂_iff_get.1 hl
    have hlen' : D.c = l.length := by simpa [parts] using hlen
    have hS : ∀ i : Fin D.c, HasSatGL w (D.σ i w).ρ (l.get (i.cast hlen')) := fun i => by
      have := hg i.1 (by simp [parts]) (by simpa [hlen'] using i.2)
      simp only [parts, List.get_eq_getElem, List.getElem_ofFn] at this
      exact hasSat_of_satV (D.discrete i) (D.loc i w) this
    refine ⟨fun i => l.get (i.cast hlen'), fun i => ⟨(hS i).1, hS i⟩, ?_⟩
    have e : List.ofFn (fun i : Fin D.c => l.get (i.cast hlen')) = l :=
      List.ext_get (by simp [hlen']) fun i h₁ h₂ => by simp
    rw [← List.sum_ofFn, e]

theorem sum_map_map (f : ℂˣ → ℂˣ) (l : List (Multiset ℂˣ)) :
    (l.map (Multiset.map f)).sum = l.sum.map f := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem forall₂_tw {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {p : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l : List (Multiset ℂˣ)} (h : List.Forall₂ (PartSat w) p l) :
    List.Forall₂ (PartSat w) (p.map (twPart χ)) (l.map (Multiset.map (· * χ.val w))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons (satV_map_mulChi hχ h) ih

theorem joinSat : PositivityTheory.Rg.BcB.F.RS.JoinSat := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D w Ba Bb hJ h1 h2 sa sb
  obtain ⟨la, fa, rfl⟩ := (pre_sat_iff Pa w Ba).1 sa
  obtain ⟨lb, fb, rfl⟩ := (pre_sat_iff Pb w Bb).1 sb
  refine (pre_sat_iff D w _).2 ⟨la.map (Multiset.map (· * χ₁.val w)) ++ lb.map (Multiset.map (· * χ₂.val w)), ?_, ?_⟩
  · rw [hJ]
    exact List.rel_append (forall₂_tw h1 fa) (forall₂_tw h2 fb)
  · rw [List.sum_append, sum_map_map, sum_map_map]

end GlobalTheory.CompanionTheory.JoinSatPf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  intro F E _ _ _ _ _ σ hσ M d b v lam hlam u S hS
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  haveI := hW 1 M
  let U1 : (Fin M → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin M) (Fv F v ⊗[F] E)).toMonoidHom u
  let U : (Fin 1 → Fin M → Fv F v ⊗[F] E)ˣ :=
    Units.map (Pi.constRingHom (Fin 1) (Fin M → Fv F v ⊗[F] E)).toMonoidHom U1
  have hc1 : distribHaarChar (Fin M → Fv F v ⊗[F] E) U1 = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin M => Fv F v ⊗[F] E) U1]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin M => Fv F v ⊗[F] E) i).toMonoidHom U1 = u :=
      fun i => Units.ext rfl
    simp only [hU, GlobalTheory.LocTateInt.distribHaarChar_Ev, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) U]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) i).toMonoidHom U = U1 :=
      fun i => Units.ext rfl
    simp only [hU, hc1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hm : coordW (Fv F v) b lam 1 M ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X) '' S) =
      distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U * coordW (Fv F v) b lam 1 M S := by
    open scoped Pointwise in
    exact (distribHaarChar_mul (coordW (Fv F v) b lam 1 M) U S).symm
  have himg : (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) =
      fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X := rfl
  rw [himg, hm, hc]
  push_cast
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompact
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

open GlobalTheory.CompanionTheory.KFin Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem matHom_mapH_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 =
      (matHom A σ J g).1.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  ext i j
  exact GlobalTheory.AutFunCompare.mat_mapH _ _ _ _ _ _

theorem map_adMat_kfin {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (X : Matrix (Fin n) (Fin r) E) :
    (X.map (inclR (F := F) A)).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = X.map (inclR (F := F) A') := by
  ext i j
  simp [inclR]

theorem flag_map_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E))
    (h : (matHom A σ J g).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 * X.map (inclR (F := F) A') =
      X.map (inclR (F := F) A') * B.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin r) (A ⊗[F] E) =>
    M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) h
  rw [Matrix.map_mul, Matrix.map_mul, map_adMat_kfin] at this
  rw [matHom_mapH_kfin]
  exact this

theorem exists_compact_iwasawa_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW
  obtain ⟨L₀, hL₀, hae⟩ := GlobalTheory.T.lattice_max_even_almost_all hCM hJ hW
  have hT : ∀ v, FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) := fun v => GlobalTheory.T.flag_transitive_of_base _ _ (GlobalTheory.T.local_hermitian_ring hCM v) (GlobalTheory.T.local_hermitian_has_base hCM v)
  have hex : ∀ v, ∃ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E),
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ ∧
      (IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) → Λ = latLoc F L₀ v) := by
    intro v
    by_cases hg : IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v)
    · exact ⟨_, hg.1, hg.2, fun _ => rfl⟩
    · obtain ⟨L, h1, h2⟩ := GlobalTheory.T.exists_max_even_adapted_lattice _ (intLoc F E v) (GlobalTheory.T.local_hermitian_ring hCM v) (hR (Fv F v) σ J) (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).1
        (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).2 (colV v X) (colV v Y) (GlobalTheory.T.local_witt_frame hCM hJ hW v)
      exact ⟨L, h1, h2, fun h => absurd h hg⟩
  choose Λ hΛ1 hΛ2 hΛ3 using hex
  have hev : ∀ᶠ v in cofinite, Λ v = latLoc F L₀ v := hae.mono fun v h => hΛ3 v h
  have hstab : ∀ v, Λ v = latLoc F L₀ v → (stabLat σ J (Λ v) : Subgroup (GLoc σ J v)) = stabLoc σ J L₀ v := by
    intro v e
    rw [e]
    rfl
  let K : Subgroup (GAd σ J) := finPts σ J ⊓ ⨅ v, (stabLat σ J (Λ v)).comap (proj σ J v)
  have memK : ∀ g, g ∈ K ↔ g ∈ finPts σ J ∧ ∀ v, proj σ J v g ∈ stabLat σ J (Λ v) := fun g => by
    simp [K, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨K, inf_le_left, ?_, ?_, ?_⟩
  ·
    obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Λ v = latLoc F L₀ v :=
      ⟨(eventually_cofinite.1 hev).toFinset, fun v hv => by simpa using hv⟩
    have hc := (isRestrGroup_GFin σ J L₀).isCompact_cyl S (fun _ => Set.univ)
      (fun v => (stabLat σ J (Λ v) : Set (GLoc σ J v))) (fun e => e.elim)
      (fun v _ => GlobalTheory.T.lattice_stabilizer_compact hCM hJ v (Λ v) (hΛ1 v).1)
    convert hc.image (continuous_ofFin σ J) using 1
    ext g
    rw [SetLike.mem_coe, memK]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ : g ∈ (ofFin σ J).range := by rwa [range_ofFin]
      refine ⟨y, ⟨fun e => e.elim, fun v _ => ?_, fun v hv => ?_⟩, rfl⟩
      · simpa using h2 v
      · rw [← hstab v (hS v hv)]
        simpa using h2 v
    · rintro ⟨y, ⟨-, h1, h2⟩, rfl⟩
      refine ⟨mem_finPts.2 (by simp), fun v => ?_⟩
      rw [proj_ofFin]
      by_cases hv : v ∈ S
      · exact h1 v hv
      · rw [hstab v (hS v hv)]
        exact h2 v hv
  ·
    intro g hg
    have hfin : {v | proj σ J v g ∉ stabLat σ J (Λ v)}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hev, eventually_proj_mem_stabLoc σ J L₀ g] with v e hv
      rw [hstab v e]
      exact hv
    let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
    choose pl kl hkl hgl Bl hBl hpl using fun v => GlobalTheory.T.max_even_lattice_flag_transitive_local (X := X) hCM hJ hW v (hT v) (Λ v) (hΛ1 v) (proj σ J v g)
    let x : ∀ v : S, GLoc σ J v := fun v => pl v
    have hp1 : embAt σ J S x ∈ minPar σ J X := by
      have : embAt σ J S x ∈ minParSub X hCM hJ hW := by
        refine Subgroup.noncommProd_mem _ (f := fun v : S => emb σ J v (x v))
          (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => ?_
        exact GlobalTheory.T.block_triangular_mem_minimal_parabolic_local (Y := Y) v.1 _ (Bl v.1) (hBl v.1) (hpl v.1)
      exact this
    have hp2 := mem_atPts.1 (embAt_mem σ J S x)
    refine ⟨embAt σ J S x, hp1, hp2.1, (embAt σ J S x)⁻¹ * g, (memK _).2 ⟨mul_mem (inv_mem hp2.1) hg, fun v => ?_⟩, by simp⟩
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · have : proj σ J v (embAt σ J S x) = pl v := proj_embAt σ J S x ⟨v, hv⟩
      rw [this, hgl v, inv_mul_cancel_left]
      exact hkl v
    · rw [hp2.2 v hv, inv_one, one_mul]
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
  ·
    rintro p ⟨B, hB, hpB⟩ hpK
    obtain ⟨hpf, hpv⟩ := (memK p).1 hpK
    obtain ⟨m, hm, ⟨d, hd⟩, ⟨d', hd'⟩, ⟨B', hB', hB1, hu⟩, hz⟩ := GlobalTheory.T.block_triangular_mem_minimal_parabolic hCM hJ hW (AF F) p B hB hpB
    have hmf : m ∈ finPts σ J := by
      refine mem_finPts.2 (Subtype.ext (Units.ext ?_))
      have e1 : (matHom _ σ J (projInf σ J m)).1 = 1 := by
        refine (matHom_mapH_kfin (fstA F) m).trans ?_
        rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change]
        have e2 : (matHom _ σ J p).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
          rw [← matHom_mapH_kfin]
          have := mem_finPts.1 hpf
          change (matHom _ σ J (projInf σ J p)).1 = 1
          rw [this, map_one]
          rfl
        rw [e2]
        exact GlobalTheory.T.levi_matrix_one hCM hJ hW _
      exact e1
    have hmK : m ∈ K := by
      refine (memK m).2 ⟨hmf, fun v => ?_⟩
      refine GlobalTheory.T.max_even_lattice_adapted_basis hCM hJ hW v (Λ v) (hΛ1 v) (hΛ2 v) (proj σ J v p) (proj σ J v m) (hpv v) _
        (hB.map _) (flag_map_kfin (evFin F v) p B hpB) ?_
      refine (matHom_mapH_kfin (evFin F v) m).trans ?_
      rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change, ← matHom_mapH_kfin]
      rfl
    refine ⟨m, ⟨d, d', hd, ?_⟩, hmK, m⁻¹ * p, ⟨B', hB', hB1, hu, fun z hz' => ?_⟩, mul_mem (inv_mem hmK) hpK, by simp⟩
    · exact hd'
    · refine hz _ ?_
      funext i
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i).symm.trans ?_
      rw [hz']
      simp

end GlobalTheory.CompanionTheory.KFin

end
end

