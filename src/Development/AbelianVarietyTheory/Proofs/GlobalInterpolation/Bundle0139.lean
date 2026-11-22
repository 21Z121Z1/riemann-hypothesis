import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.RatOrbit

theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J : Matrix n n A) (a b : n → A) :
    Formalism.UG.hform s J a b = b ⬝ᵥ Jᵀ *ᵥ (⇑s ∘ a) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, transpose_apply, Function.comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mem {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A) (J : Matrix n n A)
    (g : GL n A) (hg : g ∈ Formalism.UG.UJ s J) (a b : n → A) :
    Formalism.UG.hform s J ((g : Matrix n n A) *ᵥ a) ((g : Matrix n n A) *ᵥ b) = Formalism.UG.hform s J a b := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have h1 : ⇑s ∘ ((g : Matrix n n A) *ᵥ a) = ((g : Matrix n n A).map s) *ᵥ (⇑s ∘ a) := by
    funext i
    exact RingHom.map_mulVec s _ _ i
  rw [hform_eq, hform_eq, h1]
  conv_rhs => rw [← h]
  simp only [Formalism.UG.cT, transpose_mul, transpose_transpose, ← mulVec_mulVec]
  rw [mulVec_transpose (g : Matrix n n A), dotProduct_comm b, ← dotProduct_mulVec, dotProduct_comm]

theorem bc_mem {R A : Type} [CommRing R] [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (p : R →+* A) (s : R →+* R) (t : A →+* A) (hp : ∀ x, p (s x) = t (p x)) (J : Matrix n n R)
    (g : GL n R) (hg : g ∈ Formalism.UG.UJ s J) : Formalism.UG.bc p g ∈ Formalism.UG.UJ t (J.map p) := by
  have h : Formalism.UG.cT s (g : Matrix n n R) * J * (g : Matrix n n R) = J := hg
  show Formalism.UG.cT t ((g : Matrix n n R).map p) * J.map p * (g : Matrix n n R).map p = J.map p
  rw [← GlobalTheory.UnitarySplit.map_cond p s t hp, h]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem inclR_injective (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem smul_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : HA R σ J) (g : GL (Fin M) E)
    (hg : Formalism.UG.bc (inclR (F := F) R) g = (γ : HR R σ J).1) (x : Fin n → Fin M → E) :
    γ • ratTup (F := F) R x = ratTup (F := F) R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a) := by
  funext a i
  show (((γ : HR R σ J).1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ (ratTup (F := F) R x a)) i = _
  rw [← hg]
  exact (RingHom.map_mulVec (inclR (F := F) R) _ _ i).symm

theorem rational_sphere_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x hx
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · intro a b hab
    funext k i
    exact inclR_injective F E (congrFun (congrFun hab k) i)
  · rintro ⟨x', hx', rfl⟩
    simp only [hE, hform_eq] at hx hx'
    obtain ⟨g, hg, hgx, -⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq (c := (σ : E →+* E))
      (G := Jᵀ) two_ne_zero (sigma_sigma σ hCM) (fun a b => hJ.1 a b) hx'.symm hx
    have hU : g ∈ Formalism.UG.UJ (σ : E →+* E) J :=
      GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun z w => by rw [hform_eq, hform_eq, hg]
    have hH : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J :=
      bc_mem (inclR (F := F) (AF F)) (σ : E →+* E) (sigR (AF F) σ) (fun t => by
        simp [inclR, sigR]) J g hU
    refine ⟨(⟨_, hH⟩ : HR (AF F) σ J), ⟨g, hU, rfl⟩, ?_⟩
    refine (smul_ratTup (AF F) σ J (⟨_, hH⟩ : HR (AF F) σ J) g rfl x).trans ?_
    congr 1
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    exact hgx
  · rintro ⟨γ, ⟨g, hU, hg⟩, rfl⟩
    exact ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a, hform_mem _ J g hU _ _,
      (smul_ratTup (AF F) σ J γ g hg x).symm⟩

end GlobalTheory.RatOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
section
noncomputable section

namespace GlobalTheory.Proof.TotallyDefiniteMass

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

theorem mass_tMap {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h' (Formalism.MainNotions.StandardLattice.tMap e L) := by
  by_cases hex : ∃ s', Formalism.ThetaLiftIndependence.IsClassReps h' (Formalism.MainNotions.StandardLattice.tMap e L) s'
  · refine Formalism.MainNotions.StandardLattice.mass_transport e he L hex fun s hs => ?_
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h' _ hex]
    apply Complex.ofReal_injective
    rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
    exact Formalism.ThetaLiftIndependence.latLiftIndep K V' h' _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
  · have hex' : ¬ ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := fun ⟨s, hs⟩ => hex ⟨_, Formalism.MainNotions.StandardLattice.tMap_reps e he L s hs⟩
    unfold Formalism.HermitianLatticesTheory.mass
    rw [dif_neg hex, dif_neg hex']

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isTotDef_gram (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef) :
    IsTotDef hc.sig S.gram := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  refine ⟨hc.totReal, fun ι => ?_⟩
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  refine (Formalism.UG.Final.DefSig F E _ hc.sig S.gram ι (τ : E →+* ℂ) (RingHom.ext (hσ.2.2.2 (τ : E →+* ℂ)))
    (RingHom.ext fun a => τ.commutes a) (fun e he => (hc.fixed e).1 he)
    (Matrix.ext fun i j => (hJ S).1 i j) (hJ S).2.isUnit).2 (Or.inl ?_)
  have := h1 (τ : E →+* ℂ)
  rw [h2] at this
  simpa using this

theorem cosetSum (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef)
    (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N) :
    CosetGroupMembership.CosetSum (UFin hc S) (CosetGroupMembership.stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N) := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  have hd := isTotDef_gram hc S h1 h2
  have hτ : ∀ τ : E →+* ℂ, τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (hc.sig : E →+* E) S.gram := Matrix.ext fun i j => (hJ S).1 i j
  have hL : Submodule.IsLattice E (crdLat S N) := Formalism.MainNotions.StandardLattice.tMap_lattice (crd S) N hN
  have hf : Module.Finite (𝓞 E) (crdLat S N) := Module.Finite.iff_fg.2 hL.fg
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hm := GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ (hJ S) hd hs (crdLat S N) hf hL.span_eq_top
  have ht : Formalism.HermitianLatticesTheory.mass S.hT N =
      Formalism.HermitianLatticesTheory.mass (formJ (hc.sig : E →+* E) hs S.gram 1 :
        (Fin S.rank → E) →ₗ⋆[E] (Fin S.rank → E) →ₗ[E] E) (crdLat S N) := by
    refine mass_tMap (crd S) (fun x y => ?_) N
    rw [hT_crd hc]
    change Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • S.gram) (crd S x) (crd S y) = _
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [one_smul, smul_eq_mul, RingHom.id_apply]
    change star _ * _ = star _ * _ * _
    ring
  rw [CosetGroupMembership.stabHat_eq]
  refine ⟨Formalism.UG.Final.ClassSetFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hL.span_eq_top,
    fun y => (CosetGroupEquiv.cosetGrpEquiv _ _ y).finite_iff.2
      (Formalism.UG.Final.AdelicStabFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hL.span_eq_top y),
    fun ι _ y hy => ?_⟩
  simp only [CosetGroupEquiv.card_cosetGrp]
  exact (GlobalTheory.Mass.classMass_eq_sum_of_bijective y hy).symm.trans (hm.trans ht.symm)

theorem generalForm : CosetGroupMembership.GeneralForm :=
  fun _ _ _ _ _ _ _ _ hc S h1 h2 N hN _ => cosetSum hc S h1 h2 N hN

theorem massAsCosetSum : CosetGroupMembership.MassAsCosetSum :=
  ⟨generalForm, CosetGroupEquiv.column_of_general generalForm⟩

end GlobalTheory.Proof.TotallyDefiniteMass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeakApproximationUnitaryLatticesSplitPrime
section
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem weakApprox_split : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.MatLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem exists_lift (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} {b : L.β j} {P : rowSG Pr sel mu}
    {κ : GLint X.E (R.N j) P.1} {c : X.Kˣ} (hk : LevAt (L.levG j b) (L.levQ j b) P κ c) :
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E _ (cOf R j) x) = Loc.inX X.E _ (cOf R j) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨h, rfl⟩ := hk.1 hP
    obtain ⟨g, hg, hred⟩ := (hL.grpG j b ⟨P.1, hP⟩ _).1 h
    have hgi : g ∈ GLint X.E (R.N j) P.1 := hL.int j b P hg
    have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
    have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp j P.1 hP
      (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG j b P hP)
      _ ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ).2 fun x hx => by
        rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
    have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 (L.h j b P) := by
      have := mul_mem hg h2
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrG j b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
  · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    obtain ⟨h, rfl⟩ := hk.2 hP' hP
    have h3 := h
    rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrQ j b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩

theorem muAt_det (i : ℕ) (P : rowSG Pr sel mu) {n : ℕ} (k : GLint X.E n P.1) :
    muAt Ch sel mu cst i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
  unfold muAt rhoS
  refine LastSteps.locChar_unit _ _ ?_
  rw [(det_glint k).2, ← redGL_val]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (redGL _ P.1 k).isUnit

theorem xiEntry_invariant {u : Pr.Word} (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i)
    (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + z) = XiEntry Ch sel mu cst L i al be p p' x := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hz
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiEntry Ch sel mu cst L i al be p p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    refine hL.xiInv i hi al be P _ _ fun s l => ?_
    have h1 : frsF sel mu p P (Pi.single s 1) ∈ p.deco.1.at P.1 :=
      (frsF_mem p P _).2 ((mem_localization_standardLattice _ _).2 (GlobalTheory.TopInv.single_int s))
    have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
    have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E _ P.1 := by
      refine (frsF_mem p' P _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    have h4 := (mem_localization_standardLattice _ _).1 h3 l
    obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
    have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) (Pi.single s 1) l =
        (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) l := by
      change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P (Pi.single s 1))) l = _
      rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
    rw [h5, hc']
    convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
    push_cast
    field_simp

theorem xiEntry_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    {al : L.β i} {be : L.β (i + 1)} {γ : UF X.E (R.N i)} {γ' : UF X.E (R.N (i + 1))} {p q : ChPt (R := R) sel mu u i}
    {p' q' : ChPt (R := R) sel mu u (i + 1)}
    {κ : GLQ X.E (R.N i) (rowSG Pr sel mu)} {κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu)} {a a' : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = γ.1 * (frsF sel mu p P * ((κ P)⁻¹).1))
    (hκ' : ∀ P, frsF sel mu q' P = γ'.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1))
    (ha : ∀ P, LevAt (L.levG i al) (L.levQ i al) P (κ P) (a P))
    (ha' : ∀ P, LevAt (L.levG (i + 1) be) (L.levQ (i + 1) be) P (κ' P) (a' P)) (x : HomE X.E (R.N i) (R.N (i + 1)))
    (e0 : phiT X.K q.deco.1 q'.deco.1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT X.K p.deco.1 p'.deco.1 x) :
    XiEntry Ch sel mu cst L i al be q q' (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
      (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  have hP1 := fun P : rowSG Pr sel mu => UnfoldTwoSided.degOne_bad hX hPr hsel P
  unfold XiEntry
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu q' P) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (κ' P).1.toLinearMap ∘ₗ (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) := by
    rw [hκ, hκ']
    refine LinearMap.ext fun w => ?_
    show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 (x (γ.1.symm (γ.1 (frsF sel mu p P (((κ P)⁻¹).1 w)))))))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨r, hr, hrx, hc⟩ := exists_lift hX hPr hL (ha P).inv
  obtain ⟨r', hr', hrx', hc'⟩ := exists_lift hX hPr hL (ha' P)
  have h1 := UnfoldTwoSided.xiAt_right hP1 hL hi al be P hr hrx (inFr (frsF sel mu p P) (frsF sel mu p' P) x)
  have h2 := UnfoldTwoSided.xiAt_left hP1 hL hi al be P hr' hrx'
    (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap)
  rw [muAt_det, ← hc] at h1
  rw [muAt_det, ← hc'] at h2
  rw [e1, Pi.inv_apply, Pi.inv_apply, rhoT_inv, mul_comm (rhoS _ _ _ _ _ _), ← mul_assoc, h2, mul_assoc, h1, Units.val_mul, mul_assoc]

theorem matEquiv {u : Pr.Word} {T : ChTh W sel mu u m2} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2) (hT : ChTh.Ok (Ch := Ch) cst T) :
    MatEquiv W Ch sel mu cst L T := by
  intro i hi al be g g₁ p p'
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g₁ p'
  have key := GlobalTheory.kerOf_gmap_frames (T.th i) (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _ (hT.th i hi.le) g.1 g₁.1
    p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (XiEntry Ch sel mu cst L i al be p p')
    (XiEntry Ch sel mu cst L i al be (g • p) (g₁ • p')) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (xiEntry_invariant hPr hL hi al be p p') fun x =>
      xiEntry_law hX hPr hsel hL hi hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  unfold matK
  rw [funext hκ, funext hκ']
  refine key.trans ?_
  rw [ea, ea', mul_inv, ← map_inv (L.levG i al).chr, ← map_inv (L.levQ i al).chr]
  exact smul_comp_smul _ _ _ _ _

end GlobalTheory.MatLaw

namespace GlobalTheory.MatLaw

open GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem kAt_equiv : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i + 2 < R.m → ∀ b b' (g : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).G b) (g' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).G b') (d : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).D b) (d' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).D b'), kAt W Ch sel mu cst L A u i b b' (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).actD b; g • d) (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).actD b'; g' • d') = (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).rho X.emb (W.lamTrue u i) b g⁻¹ := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A hX hPr _ hsel hT hg hL _ hTh hi b b' g g' d d'
  have hm := hL.hm
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (Idx.of_get b (by omega) _).symm⟩
  obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
  have e : ∀ p p', kAt W Ch sel mu cst L A u i (Idx.of al (by omega)) (Idx.of be (by omega)) p p' =
      matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) i al be p.1.1 p'.1.1 := fun p p' => by
    rw [matK_eq_xiAt W Ch sel mu cst L _ hi]
    unfold kAt KerT.ker
    rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u i (by omega)]
    rfl
  rw [e, e]
  exact matEquiv hX hPr hsel ⟨hT, hg⟩ hL hTh i (by omega) al be g g' d.1.1 d'.1.1

end GlobalTheory.MatLaw

end
end

