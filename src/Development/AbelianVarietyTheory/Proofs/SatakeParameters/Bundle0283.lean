import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0272
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open scoped Pointwise

namespace GlobalTheory.AboveL

theorem mem_dec_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) :
    g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := K') A := by
  have key : ((g • A : ValuationSubring Ω) : Set Ω) = ((g' • A : ValuationSubring Ω) : Set Ω) := by
    rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]
  unfold Dec
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; apply SetLike.coe_injective; rw [← key]; exact congrArg _ h
  · intro h; apply SetLike.coe_injective; rw [key]; exact congrArg _ h

theorem exists_cm_solvable_split : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  intro Ω _ E _ _ _ _ _ A w h N hN
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := Ideal.comap_ne_bot_of_integral_mem hx₀0 hx₀ (Algebra.IsIntegral.isIntegral x₀) }
  have hv : IsPlaceOver A v := by
    intro x
    show _ ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [← h]
    rfl
  obtain ⟨T, hvT, hlift⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hN

  let φ := IsScalarTower.toAlgHom F E Ω
  let K : IntermediateField F Ω := φ.fieldRange
  haveI : FiniteDimensional F K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  have hK : ∀ g : G F Ω, g ∈ K.fixingSubgroup ↔ ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x; exact hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩; exact hg x
  let V : Subgroup (Dec (F := F) A) := K.fixingSubgroup.subgroupOf (Dec (F := F) A)
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
  haveI : Fact (Nat.card (E ≃ₐ[F] E)).Prime :=
    ⟨by rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E]; exact Nat.prime_two⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card rfl
  have habel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ := fun σ τ => (IsCyclic.commGroup).mul_comm σ τ
  have hcomm : commutator (Dec (F := F) A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mem_subgroupOf, hK]
    intro x
    have h1 : AlgEquiv.restrictNormalHom (K₁ := Ω) E ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [habel (AlgEquiv.restrictNormalHom E (a : G F Ω)) (AlgEquiv.restrictNormalHom E (b : G F Ω))]
      group
    have h2 := AlgEquiv.restrictNormal_commutes ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E x
    have h3 : AlgEquiv.restrictNormal ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E = 1 := h1
    rw [← h2, h3]
    rfl
  obtain ⟨F₁, hF₁fin, hF₁ab, hF₁real, hF₁dec, hF₁T⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F A v hv V hVo hcomm T hvT
  obtain ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, hfix, hsub⟩ :=
    hlift F₁ hF₁fin inferInstance (isSolvable_of_comm fun a b => hF₁ab.toIsMulCommutative.is_comm.comm a b) hF₁real hF₁T
  have hkey : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ z ∈ F₁, g z = z) →
      ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g hg hz
    exact (hK g).1 (Subgroup.mem_subgroupOf.1 ((hF₁dec ⟨g, hg⟩).1 ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hz)))
  have hkey2 : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) →
      ∀ z ∈ F₁, g z = z := by
    intro g hg hE
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hF₁dec ⟨g, hg⟩).2 (Subgroup.mem_subgroupOf.2 ((hK g).2 hE)))
  refine ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, ?_, ?_⟩
  · intro g hg
    apply (hfix g).2
    let g' : G F Ω := g.restrictScalars F
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    exact hkey2 g' hg' (fun x => g.commutes x)
  · intro g hg
    have hfixP : ∀ x ∈ maximalRealSubfield M, g (algebraMap M Ω x) = algebraMap M Ω x :=
      fun x hx => g.commutes ⟨x, hx⟩
    have hF1 : ∀ z ∈ F₁, g z = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hsub z hz
      exact hfixP x hx
    have hFfix : ∀ y : F, g.toRingEquiv (algebraMap F Ω y) = algebraMap F Ω y :=
      fun y => hF1 _ (F₁.algebraMap_mem y)
    let g' : G F Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hFfix
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    have hE : ∀ x : E, g.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := hkey g' hg' hF1
    let g'' : G E Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hE
    exact (hfix g'').2 hF1

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  first | exact @GlobalTheory.BadPrimes.lev_pos_and_noConj | exact GlobalTheory.BadPrimes.lev_pos_and_noConj | (intros; apply GlobalTheory.BadPrimes.lev_pos_and_noConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChangesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  first | exact @GlobalTheory.TwV.datLoc_of_move | exact GlobalTheory.TwV.datLoc_of_move | (intros; apply GlobalTheory.TwV.datLoc_of_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderHeckeCharGalois
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.HeckeToGal

theorem exists_galChar_of_finite_order : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (η : HChar K) (n : ℕ), 0 < n → η ^ n = 1 → ∃ χ : G K Ω →* ℂˣ,
      IsOpen (χ.ker : Set (G K Ω)) ∧ (χ = 1 → η = 1) ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
        IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v := by
  intro Ω _ K _ _ _ _ η n hn hη
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have hηn : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar K => ξ.1 x) hη
  have hopen : IsOpen (η.1.ker : Set (Ideles K)) := isOpen_ker_of_pow η.1 η.2.1 hn hηn
  have hinf : infConn K ≤ η.1.ker := by
    rintro _ ⟨y, hy, rfl⟩
    let φ : (InfiniteAdeleRing K)ˣ →* ℂˣ :=
      η.1.comp (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))
    have hc : Continuous fun z : InfiniteAdeleRing K => (z, (1 : FiniteAdeleRing (𝓞 K) K)) :=
      continuous_id.prodMk continuous_const
    have hφ : Continuous φ := η.2.1.comp (Continuous.units_map _ hc)
    have hop : IsOpen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := isOpen_ker_of_pow φ hφ hn (fun x => hηn _)
    have hcl : IsClopen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
    exact hcl.connectedComponent_subset (one_mem φ.ker) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (Subgroup.isClosed_of_isOpen _ hopen)
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (η.2.2 k)
  have hs : Function.Surjective art := ha.quot.surjective
  let ηb : Gab K Ω →* ℂˣ :=
    art.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩
  have hηb : ∀ x, ηb (art x) = η.1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply art (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩ x
  have hηbc : Continuous ηb := by
    refine ha.quot.isQuotientMap.continuous_iff.mpr ?_
    have e : (ηb ∘ art) = η.1 := funext hηb
    rw [e]
    exact η.2.1
  let χ : G K Ω →* ℂˣ := (ηb.comp (toAb K Ω))⁻¹
  have hχ : ∀ σ, χ σ = (ηb (toAb K Ω σ))⁻¹ := fun σ => rfl
  have hχc : Continuous χ := by
    have ht : Continuous (toAb K Ω) := (QuotientGroup.isQuotientMap_mk _).continuous
    exact (hηbc.comp ht).inv
  have hχn : ∀ σ, χ σ ^ n = 1 := fun σ => by
    obtain ⟨x, hx⟩ := hs (toAb K Ω σ)
    rw [hχ, ← hx, hηb, inv_pow, hηn, inv_one]
  refine ⟨χ, isOpen_ker_of_pow χ hχc hn hχn, fun h1 => ?_, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
    have e := DFunLike.congr_fun h1 σ
    rw [hχ, hσ, hηb, MonoidHom.one_apply, inv_eq_one] at e
    exact e
  · filter_upwards [(GlobalTheory.Mem.UnrAe.unr_ae_and_level K η).1] with v hv
    intro A σ hA hσ
    obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
    rw [hχ, ← map_inv, ← map_inv, ← e, hηb, ← η.val_eq hv x hx]
    rfl

end GlobalTheory.HeckeToGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepLevelLocalElementsValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStep_level_local_elements_values : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  first | exact @GlobalTheory.TwV.levSrc_localData | exact GlobalTheory.TwV.levSrc_localData | (intros; apply GlobalTheory.TwV.levSrc_localData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalConditionInvariantRightLevelTranslateStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  first | exact @GlobalTheory.funMoved_mul_level | exact GlobalTheory.funMoved_mul_level | (intros; apply GlobalTheory.funMoved_mul_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemPeriodLatticeIffStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), ∀ x : HomE D.host.E a b, seamHom s x ∈ perO (ambOf s B χ cD).AA N N' ↔ x ∈ perO (aaOf D cc) (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.TwV.SeamPer.seamHom_mem_perO | exact GlobalTheory.TwV.SeamPer.seamHom_mem_perO | (intros; apply GlobalTheory.TwV.SeamPer.seamHom_mem_perO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIffStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  first | exact @GlobalTheory.SeamTwist.seamHom_mem_twO | exact GlobalTheory.SeamTwist.seamHom_mem_twO | (intros; apply GlobalTheory.SeamTwist.seamHom_mem_twO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.DepthZeroRec

theorem inePol_lpTw_of_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (y : WD h) (s : ℝ) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    (y.lpTw s).inePol σ = y.inePol σ := by
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk]
  congr 1
  show ((unrChar h (qPow w s) (ineIncl h ⟨σ, hσ⟩) : ℂˣ) : ℂ) • b.ρ (ineIncl h ⟨σ, hσ⟩) = _
  rw [WeilDeligne.unrChar_apply, deg_ineIncl, zpow_zero, Units.val_one, one_smul]

end GlobalTheory.RoadU.DepthZeroRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriNeBotOfSpherical
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.LimitAtL

theorem mem_fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {H : Subgroup G} {v : V} : v ∈ GlobalTheory.PRep.fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* kˣ) h : k) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]
  {a : ℕ}

end GlobalTheory.Cong.LimitAtL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JumpsDescend

theorem jumps_descend : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (O' : Type) [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → Bw'.j = Bw.j → ∀ (τ : K →+* Qbar l) (τL : L →+* Qbar l), τL.comp (algebraMap K L) = τ → ∀ J : Multiset ℤ, IsJumpsAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) τL J → IsJumpsAt P Bw (r.comp (Dec (F := K) A).subtype) τ J := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' _ _ l _ P AI hT a r hr O _ _ _ Bw O' _ _ _ Bw' hj hj' hjj τ τL hτL J hJ
  obtain ⟨T⟩ := hT

  have hle : Bw.Kw.1 ≤ Bw'.Kw.1 := by
    rw [BridgeInd.kw_eq_adjoin Bw, BridgeInd.kw_eq_adjoin Bw', IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
    show Bw'.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
    rw [hjj, ← IsScalarTower.algebraMap_apply]
  have hJ0 := hJ
  obtain ⟨LL', r', hmod', hdR', τ₁, hi₁, -⟩ := hJ
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨L₁, hL₁, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont (supExt Bw.LL LL')
  have hBL : Bw.LL.1 ≤ L₁.1 := (le_sup_left : Bw.LL.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  have hLL : LL'.1 ≤ L₁.1 := (le_sup_right : LL'.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L₁ hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥L₁.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) L₁ rE := by
    refine ⟨hBL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodM : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hmod'.1.trans hLL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hle L₁ rE
  have hdM : Bw'.IsdRE P L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodM.isdRAt_iff P).1 ⟨LL', r', hmod', hdR'⟩
  have hdR2 : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE L₁ rE) hle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdM
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE L₁ rE) := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hle (Bw.repE L₁ rE) T).2 hdR2
  have hdE : Bw.IsdRE P L₁ rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this

  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := (IntermediateField.inclusion hLL).comp τ₁
  have hiM : IsInduced Bw' τL τ'' := fun x => hi₁ x
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := τ''.comp (IntermediateField.inclusion hle)
  have hτ₂ : IsInduced Bw τ τ₂ := by
    intro x
    have e1 : (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩ : ↥Bw'.Kw.1) =
        ⟨Bw'.j (algebraMap L Ω (algebraMap K L x)), Bw'.j_E (algebraMap K L x)⟩ := by
      apply Subtype.ext
      show Bw.j (algebraMap K Ω x) = Bw'.j (algebraMap L Ω (algebraMap K L x))
      rw [hjj, ← IsScalarTower.algebraMap_apply]
    show τ x = ((τ'' (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩) : ↥L₁.1) : Om l)
    rw [e1, ← hτL]
    exact hiM (algebraMap K L x)
  refine ⟨L₁, rE, hmodE, hdE, τ₂, hτ₂, fun n => ?_⟩
  rw [IsJumpsAt.count_eq P hmodM hiM hJ0 n]
  unfold LocBridge.multE
  rw [hrep]
  exact GlobalTheory.JumpRestrict.multV_restrict l P AI T Bw.Kw Bw'.Kw L₁ hle (Fin a → ↥L₁.1) (Bw.repE L₁ rE) hdR τ'' n

end GlobalTheory.JumpsDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_true_ent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.ent = E ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  obtain ⟨t, ht, hO, -, hTop⟩ := GlobalTheory.T.kernelEntries_compatible_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  exact kerEntTied_withEnt I l Z O E hE hS t ht hO hTop

end GlobalTheory.Mem.Col2.TC
end

