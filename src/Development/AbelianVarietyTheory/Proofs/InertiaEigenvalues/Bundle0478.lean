import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Quad

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
    have hx : a • x = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨fun _ => 1, ?_⟩
      funext j
      simp [Algebra.smul_def, mul_inv_cancel₀ ha']
    let x' : Submodule.torsionBy O (KOG O 1) a := ⟨x, hx⟩
    let f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a := LinearMap.toSpanSingleton O _ x'
    have hf : Ideal.span {a} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨b, hb⟩ := hy
      refine ⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩
      change b 0 • x = Submodule.Quotient.mk y
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0 := by
        simpa [Algebra.smul_def] using congrFun hb 0
      simp only [Pi.smul_apply, Algebra.smul_def, h0]
      field_simp

theorem eq_zero_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {γ : G E Ω} (hγ : TameGenAt A γ) {M : Type} [AddCommGroup M] (f : G E Ω → M)
    (hf : IsLocallyConstant f) (hadd : ∀ a ∈ Ine (F := E) A, ∀ b ∈ Ine (F := E) A, f (a * b) = f a + f b)
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → f σ = 0) (h0 : f γ = 0)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : f σ = 0 := by
  have h1 : f 1 = 0 := by simpa using hadd 1 (one_mem _) 1 (one_mem _)
  let K : Subgroup (G E Ω) :=
    { carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨one_mem _, h1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hadd a ha.1 a⁻¹ (inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, zero_add] at this
        exact this.symm⟩ }
  refine closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)
  intro g hg
  refine ((Subgroup.closure_le K).2 ?_ hg).2
  rintro g (rfl | hg)
  · exact ⟨hγ.1, h0⟩
  · exact ⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : GoodCongruenceObjects D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.Quad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
section
noncomputable section

namespace GlobalTheory.Pass.LocDirect

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRing : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

def ModuleGaloisRepresentation {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

abbrev fam (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) :=
  Br.loc D.nbr i w hw (rTwO D.nd i r x)

def toLLv {a n : ℕ} (y : Fin a → Fin n → KK D.nd i) : Fin a → Fin n → Br.LL D.nbr i w hw :=
  fun j m => Br.toLLK (D.nbr i w hw) (y j m)

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun m => Br.toLLK (D.nbr i w hw) (v m)) =
      fun m => Br.toLLK (D.nbr i w hw)
        ((mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).mulVec v m) := by
  funext m
  rw [RingHom.map_mulVec]
  congr 1
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def XV {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (toLLv i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem XV_stable {a : ℕ} (x : Fin a → D.nd.X i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (g : Br.G D.nbr i w hw) :
    ∀ u ∈ XV i w hw Y, sumRho (fun j : Fin a => fam i w hw r (x j)) id g u ∈ XV i w hw Y := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨_, hst ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) y hy, ?_⟩
    funext j
    rw [sumRho_apply]
    exact (loc_mulVec i w hw _ g (y j)).symm
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

def Xgrep {a : ℕ} (x : Fin a → D.nd.X i)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GRep.sub (GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) (fun j : Fin a => fam i w hw r (x j))
    (fun j v => (hc j).matrix_mulVec continuous_const) id) (XV i w hw Y) (XV_stable i w hw r x Y hst)

def pushSet {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) {a : ℕ} (x : Fin a → D.nd.X i)
    (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (hE : ∀ γ : GE D.nd,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y) :
    Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  {c | ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
      c = fun g => Br.phi (D.nbr i w hw) k
        (φ ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩)}

theorem mem_cutCoc (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (c : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :
    c ∈ cutCoc i w hw r Xs M ↔ ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      c ∈ pushSet i w hw r M x E Y hst hE := Iff.rfl
end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCupPairingReducedCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.CupAbove

theorem cup_mem_of_span {R Γ M M' P : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (π : Representation R Γ M) (π' : Representation R Γ M') (μ : Representation R Γ P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (π g x) (π' g y) = μ g (b x y)) (hc : ContAction π')
    (W : Submodule R (Z2 μ)) (hW : (B2 μ).comap (Z2 μ).subtype ≤ W) (S : Set (H1 π)) (S' : Set (H1 π'))
    (h : ∀ s ∈ S, ∀ s' ∈ S', ∃ z z', s = Submodule.Quotient.mk z ∧ s' = Submodule.Quotient.mk z' ∧
      cupCocycleZ1Z1 π π' μ b hb hbe hc z z' ∈ W)
    (x : Z1 π) (y : Z1 π') (hx : Submodule.Quotient.mk x ∈ Submodule.span R S)
    (hy : Submodule.Quotient.mk y ∈ Submodule.span R S') : cupCocycleZ1Z1 π π' μ b hb hbe hc x y ∈ W := by
  have e : ∀ z z', cupProductH1H1 π π' μ b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.mkQ _ (cupCocycleZ1Z1 π π' μ b hb hbe hc z z') := fun _ _ => rfl
  have h1 : Submodule.map₂ (cupProductH1H1 π π' μ b hb hbe hc) (Submodule.span R S) (Submodule.span R S') ≤
      W.map (Submodule.mkQ _) := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨s, hs, s', hs', rfl⟩
    obtain ⟨z, z', rfl, rfl, hz⟩ := h s hs s' hs'
    exact ⟨_, hz, (e z z').symm⟩
  have h2 := h1 (Submodule.apply_mem_map₂ _ hx hy)
  rw [e, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hW] at h2
  exact h2

def addCob {K Γ A : Type} [CommRing K] [Group Γ] [TopologicalSpace Γ] [TopologicalSpace K] [DiscreteTopology K]
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (μ : Representation K Γ K) (χ : Γ → A) : Submodule K (Z2 μ) where
  carrier := {z | ∀ lam : K →+ A, ∃ a : Γ → A, Continuous a ∧ ∀ g h, lam (z.1 (g, h)) = χ g * a h - a (g * h) + a g}
  zero_mem' := fun lam => ⟨0, continuous_const, fun g h => by simp⟩
  add_mem' := fun {z z'} hz hz' lam => by
    obtain ⟨a, ha, h1⟩ := hz lam
    obtain ⟨a', ha', h2⟩ := hz' lam
    refine ⟨a + a', ha.add ha', fun g h => ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply, map_add, h1, h2]
    ring
  smul_mem' := fun k z hz lam => hz (lam.comp (AddMonoidHom.mulLeft k))

theorem map_padic_mul {l : ℕ} [Fact l.Prime] {K : Type} [CommRing K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
    (lam : K →+ ZMod (l ^ 1)) (u : ℤ_[l]) (k : K) : lam (φ u * k) = PadicInt.toZModPow 1 u * lam k := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 u)
  have h1 : φ u = (u.appr 1 : ℕ) := by
    have := congrArg φ hc
    rw [map_mul, map_pow, map_natCast, hl, map_sub, map_natCast, pow_one, mul_zero] at this
    exact sub_eq_zero.1 this.symm
  have h2 : PadicInt.toZModPow 1 u = (u.appr 1 : ℕ) := rfl
  rw [h1, h2, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

section Galois

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}

theorem mk_eq_zero_iff (w : Z2 (muLoc F l 1 A)) : (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 ↔
    ∃ a : Dec (F := F) A → ZMod (l ^ 1), Continuous a ∧ ∀ g h : Dec (F := F) A, w.1 (g, h) =
      PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * a h - a (g * h) + a g := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine exists_congr fun a => and_congr_right fun _ => ⟨fun e g h => (congrFun e (g, h)).symm, fun e => ?_⟩
  funext ⟨g, h⟩
  exact (e g h).symm

variable {K : Type} [CommRing K] [TopologicalSpace K] [DiscreteTopology K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
  (μ : Representation K (Dec (F := F) A) K) (hμ : ∀ g k, μ g k = φ ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * k)

include hl hμ

theorem exists_push (z : Z2 μ) (lam : K →+ ZMod (l ^ 1)) : ∃ w : Z2 (muLoc F l 1 A), ∀ g h, w.1 (g, h) = lam (z.1 (g, h)) := by
  refine ⟨⟨fun p => lam (z.1 p), continuous_of_discreteTopology.comp z.2.1, fun g h k => ?_⟩, fun _ _ => rfl⟩
  have e := congrArg lam (z.2.2 g h k)
  rw [map_sub, map_add, map_sub, hμ, map_padic_mul φ hl, map_zero] at e
  exact e

theorem coboundaries_le_cyclotomic_additive : (B2 μ).comap (Z2 μ).subtype ≤
    addCob μ (fun g => PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) := by
  rintro z ⟨c, hc, e⟩ lam
  refine ⟨fun g => lam (c g), continuous_of_discreteTopology.comp hc, fun g h => ?_⟩
  have e' : z.1 (g, h) = μ g (c h) - c (g * h) + c g := (congrFun e (g, h)).symm
  rw [e', map_add, map_sub, hμ, map_padic_mul φ hl]

end Galois

theorem mk_eq_zero_of_rational (hT : LocalTateDuality) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (β : O →+ ZMod (l ^ 1)) (z : Dec (F := F) A → Dec (F := F) A → O) (f : Dec (F := F) A → ↥Bw.LL.1) (hf : Continuous f)
    (hz : ∀ g h, Bw.toLL (z g h) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g)
    (w : Z2 (muLoc F l 1 A)) (hw : ∀ g h, w.1 (g, h) = β (z g h)) :
    (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  have : IsGalois F Ω := {}
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have : IsTopologicalRing ↥Bw.LL.1 := inferInstanceAs (IsTopologicalRing ↥Bw.LL.1.toSubfield.toSubring)
  have hr : Set.range Bw.toLL = Set.range (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1) :=
    Bw.eO.surjective.range_comp (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1)
  obtain ⟨n, a, ha, e⟩ := GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' (Dec (F := F) A) l (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) O ↥Bw.LL.1 Bw.toLL
    (GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw) (hr ▸ GlobalTheory.LocalIntegers.isOpen_integers l Bw.LL)
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    (fun x => by
      obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL (fun (_ : Unit) (_ : Fin 1) => x)
        continuous_const
      exact ⟨n, hr ▸ ⟨⟨_, hn () 0⟩, rfl⟩⟩) β z f hf hz
  refine GlobalTheory.T.mu_cocycle_coboundary_lift hT F Ω l A v hA n w a ha fun g h => ?_
  rw [hw]
  exact e g h

section Matrices

variable {Γ O K : Type} [Group Γ] [CommRing O] [CommRing K] [Algebra O K] {r : ℕ}

theorem repOn_one_apply (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    repOn ρ (1 : Γ →* Kˣ) K g m = (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equivariant (T T' : Matrix (Fin r) (Fin r) O) (hT : IsUnit T.det) (u : O) (h : T' = u • T⁻¹.transpose)
    (x y : Fin r → K) :
    (T.map (algebraMap O K)).mulVec x ⬝ᵥ (T'.map (algebraMap O K)).mulVec y = algebraMap O K u * (x ⬝ᵥ y) := by
  have e : (T.map (algebraMap O K)).transpose * T'.map (algebraMap O K) = algebraMap O K u • 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.mul_smul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hT, Matrix.transpose_one]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_generators (T : Matrix (Fin r) (Fin r) O) (y y' : Fin r → O) (b b' : K) :
    (fun a => algebraMap O K (y a) • b) ⬝ᵥ (T.map (algebraMap O K)).mulVec (fun a => algebraMap O K (y' a) • b') =
      (b * b') * algebraMap O K (y ⬝ᵥ T.mulVec y') := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Matrices

theorem cup_eq_zero_above : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  intro hT D N X bkP i s _ K _ _ _ _ hK ρ hρ v hv x y hx hy lam w hw
  let φ : ℤ_[X.l i] →+* K := (algebraMap (X.O0 i) K).comp (algebraMap ℤ_[X.l i] (X.O0 i))
  have hl : ((X.l i : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap (X.O0 i) K)]
    exact hK _ (GlobalTheory.PrimeToInertia.l_mem i)
  let μ : Representation K (DecV N v) K :=
    charRep (((Units.map (algebraMap (X.O0 i) K).toMonoidHom).comp (eps0 X i)).comp (DecV N v).subtype)
  have hμ : ∀ (g : DecV N v) k, μ g k = φ ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) * k := fun _ _ => rfl
  have hbe : ∀ (g : DecV N v) (m m' : Fin D.R.r → K),
      dotProductBilin K K (((red i K (Tgl i s)).comp (DecV N v).subtype) g m) (((red i K ρ).comp (DecV N v).subtype) g m') =
        μ g (dotProductBilin K K m m') := by
    intro g m m'
    change red i K (Tgl i s) g m ⬝ᵥ red i K ρ g m' = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (m ⬝ᵥ m')
    rw [repOn_one_apply, repOn_one_apply]
    refine dot_equivariant _ _ (Matrix.isUnits_det_units _) _ ?_ m m'
    rw [hρ, Tgl_coe]
    rfl
  have hc : ContAction ((red i K ρ).comp (DecV N v).subtype) := by
    have : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
      by_contra hn
      exact ha.ne_zero (hK a hn)⟩
    have h1 : ContAction (red i K ρ) := by
      refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun c hc => ?_⟩
      · simp_rw [show ∀ g, _ from hρ]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
      · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hc
        rw [hc, zero_smul]
    exact h1.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop)
  rw [bkOn, dif_pos hv] at hx hy
  have key := cup_mem_of_span _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc _
    (coboundaries_le_cyclotomic_additive φ hl μ hμ) _ _ (by
      rintro _ ⟨z, c, t, b, h1, h2, h3, rfl⟩ _ ⟨z', c', t', b', h1', h2', h3', rfl⟩
      refine ⟨z, z', rfl, rfl, fun lam => ?_⟩
      obtain ⟨f, hf, e⟩ := GlobalTheory.T.cup_coboundary_alt D N X bkP i s ‹_› ρ hρ v hv c c' t t' h1 h1' h2 h2'
      obtain ⟨w, hw⟩ := exists_push φ hl μ hμ
        (cupCocycleZ1Z1 _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc z z') lam
      simp_rw [← hw]
      refine (mk_eq_zero_iff w).1 (mk_eq_zero_of_rational hT (N.plOm.2 v) (bkP.br i v hv)
        ((lam.comp (AddMonoidHom.mulLeft (b * b'))).comp (algebraMap (X.O0 i) K).toAddMonoidHom) _ f hf e w fun g h => ?_)
      rw [hw]
      change lam (z.1 g ⬝ᵥ red i K ρ g (z'.1 h)) = lam (b * b' * algebraMap (X.O0 i) K _)
      rw [repOn_one_apply, show z.1 g = _ from funext (h3 g), show z'.1 h = _ from funext (h3' h), dot_generators])
    x y hx hy
  obtain ⟨a, ha, e⟩ := key lam
  exact (mk_eq_zero_iff w).2 ⟨a, ha, fun g h => (hw g h).trans (e g h)⟩

end GlobalTheory.CupAbove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReductionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  first | exact @GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | exact GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | (intros; apply GlobalTheory.BKTorsionRed.mem_HfQ_iff_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibnizStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative K))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  first | exact @GlobalTheory.BKReal.Conn.pow_apply_smul | exact GlobalTheory.BKReal.Conn.pow_apply_smul | (intros; apply GlobalTheory.BKReal.Conn.pow_apply_smul <;> assumption)
end

